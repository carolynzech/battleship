#lang forge "curiosity modeling" "le4s1dpsmgywfv79@gmail.com"

abstract sig Boolean {}
one sig True, False extends Boolean {}

// Links the Boards together
one sig Game {
   initial: one Board,
   next: pfunc Board -> Board // next Board in the trace
}

// sig for cells on the Board
abstract sig Space {}

// A cell on the Board that contains 1/2 of a Boat
sig BoatSpot extends Space {}
// A cell on the Board where the player tried to strike a BoatSpot, but missed
sig MissedStrike extends Space {}

// note that there is no "Empty" sig--we made this modeling choice because it takes less storage to just write 
// "no b.board" for some Board b than to have a bunch of Empty objects

// Boats are comprised of two adjacent BoatSpots
sig Boat {
    spot1: one BoatSpot,
    spot2: one BoatSpot
}

// Represents the state of the game
sig Board {
    board: pfunc Int -> Int -> Space, // row index -> column index -> Space
    boats: set Boat, // set of boats that belong to this Board
    hit_boatspots: func BoatSpot -> Boolean, // for each BoatSpot, maps to True if it has been hit in this state, false otherwise
    has_lost: one Boolean // True if the player has lost the game, False otherwise
}

// Each Board is required to be wellformed. All other predicates should be run in combination with this one.
pred wellformed[b: Board] {

    // each board has three boats
    #{boat: Boat | boat in b.boats} = 3
    
    // check for valid dimensions
    all row, col : Int | {
        (row < 0 or col < 0 or row > 5 or col > 5) implies (no b.board[row][col])
    }

    // the space can't show up more than once on a given player's board
    all space: Space | {
        all row, col, row2, col2 : Int | (row != row2 or col != col2) implies {
            b.board[row][col] = space implies (b.board[row2][col2] != space)
        }
    }

    all disj boat, boat2: Boat | (boat in b.boats and boat2 in b.boats) implies {
        // each boat has two boatspots
        one boat.spot1
        one boat.spot2

        // spot at spot1 can't be the same as spot at spot2
        boat.spot1 != boat.spot2
        
        // spot belonging to one boat can't belong to any other boat
        boat.spot1 != boat2.spot1
        boat.spot1 != boat2.spot2
        boat.spot2 != boat2.spot2
        boat.spot2 != boat2.spot1

        // BoatSpots of this boat are positioned vertically or horizontally -- no diagonal
        all row, col: Int | (b.board[row][col] = boat.spot1) implies {
            (b.board[row][add[col,1]] = boat.spot2 or b.board[row][add[col,-1]] = boat.spot2 or b.board[add[row,1]][col] = boat.spot2 or b.board[add[row,-1]][col] = boat.spot2)
        }
    }
    // has_lost is only true if final is true
    b.has_lost = True iff final[b]
}

// Checks if Board b is a valid initial state
pred init[b: Board] {
    // no MissedStrikes on initial board
    all row, col : Int | {
        no ms : MissedStrike | {
            b.board[row][col] = ms
        }
    }

    // all BoatSpots must be present on the initial board, and none are hit. This contraint, combined with the constraints in 
    // move and doNothing about the board, ensures that every BoatSpot is present in the same spot on every board.
    all spot : BoatSpot | {
        some row, col : Int | {
            b.board[row][col] = spot
            b.board[row][col] = spot implies b.hit_boatspots[spot]= False
        }
    }
    // player hasn't lost
    b.has_lost = False
}

// Checks if Board b is a valid final state, i.e., if all boats are sunk
pred final[b: Board] {
    // all boat spots on Board's board are hit
    all spot : BoatSpot | {
        b.hit_boatspots[spot] = True
    }
}

// Helper predicate for move. Checks that (row, col) is a valid spot for a move on Board b
// A spot is valid if it is on the board and if it contains 1) an empty space or 2) a BoatSpot that has not yet been hit
pred validLocation[row: Int, col: Int, b: Board] {
    // on board
    (row >= 0 and col >= 0 and row <= 5 and col <= 5)
    // either empty or boat spot that isn't hit
    (no b.board[row][col]) or (some spot: BoatSpot | (b.board[row][col] = spot and b.hit_boatspots[spot] = False))
}

// True if there is a valid move from pre to post by striking pre.board[row][col], false otherwise
pred move[pre: Board, post: Board, row: Int, col: Int] {

    // GUARD
    validLocation[row, col, pre]
    not final[pre] // can't move from final state

    // ACTION
    // If the place we're moving is a boatspot:
    some pre.board[row][col] implies {
        post.board[row][col] = pre.board[row][col] // boatspot remains in place
        pre.hit_boatspots[pre.board[row][col]] = False // boatspot hasn't yet been hit
        post.hit_boatspots[post.board[row][col]] = True // set hit to true
    } else {
        // if striking empty location, MissedStrike should be in the post board
        some ms : MissedStrike | {
            post.board[row][col] = ms
        }
        pre.hit_boatspots = post.hit_boatspots // no boatspot should be hit
    }

    // MAINTAIN PREVIOUS/UNINVOLVED fields

    // either one boatspot is hit (board[row][col] is a boatspot) or none are (board[row][col] is an empty space)
    // since we check that there's no change for the empty space case, this is really just a fast way to check that
    // only one boatspot was hit without having to loop over all other row, col in the some pre.board[row][col] case
    #{spot : BoatSpot | pre.hit_boatspots[spot] != post.hit_boatspots[spot]} <= 1

    // all other spaces on the board stays the same
    all row2, col2 : Int | (row != row2 or col != col2) implies {
        post.board[row2][col2] = pre.board[row2][col2]
    }
}

// True if nothing has changed between pre and post. Used once the game is over but the trace has more boards
pred doNothing[pre: Board, post: Board] {
    -- GUARD
    pre.has_lost = True // should only doNothing if the game is already over

    -- ACTION
    // board shouldn't change
    all row, col: Int | 
        post.board[row][col] = pre.board[row][col]
    
    // hit_boatspots shouldn't change
    #{spot : BoatSpot | pre.hit_boatspots[spot] != post.hit_boatspots[spot]} = 0
    
    post.has_lost = True
}

// Create Board traces
pred traces {
    init[Game.initial]
    
    // initial is actually the first state
    all b : Board | {
        Game.next[b] != Game.initial
    }

    all b: Board | some Game.next[b] implies {
        some row, col: Int | {
            move[b, Game.next[b], row, col]            
        }
        or
            doNothing[b, Game.next[b]]
    }

}

 -------------- EXAMPLES FOR STERLING  -------------- 

// One wellformed Board. We'd recommend running this first to get a sense of the sigs and how they work together.
// Each property enforced in the wellformed predicate is commented, so you can check that they all hold in the evaluator
// run {
//     all b : Board | wellformed[b]
// } for exactly 1 Board, exactly 3 Boat, exactly 6 BoatSpot for {next is linear}

// One wellformed initial Board
// Some properties you can observe in the evaluator are:
//      -- no MissedStrikes on the board
//      -- b.hit_boatspots maps to False for all BoatSpots
//      -- b.has_lost is False
// run {
//     all b : Board | wellformed[b] and init[b]
// } for exactly 1 Board, exactly 3 Boat, exactly 6 BoatSpot for {next is linear}

// One wellformed final Board
// Some properties you can observe in the evaluator are:
//      -- b.hit_boatspots maps to True for all BoatSpots
//      -- b.has_lost is True
// run {
//     all b : Board | wellformed[b] and final[b]
// } for exactly 1 Board, exactly 3 Boat, exactly 6 BoatSpot for {next is linear}

// One wellformed Board with a valid (row, col) proposed to move
// Some properties you can observe in the evaluator are:
//      -- (2, 3) is within the board
//      -- b.board[2][3] is either a BoatSpot or does not exist (empty space)
//      -- if b.board[2][3] is a BoatSpot, b.hit_boatspots[b] is False
// run {
//     some pre, post : Board | wellformed[pre] and wellformed[post] and move[pre, post, 2, 3]
// } for exactly 2 Board, exactly 3 Boat, exactly 6 BoatSpot for {next is linear}

// A trace of 10 wellformed Boards.
// We miss 3 times, so 9 moves - 3 misses implies that the other 6 moves are all hits, which in turn implies that only the last board is a final board
// See README for an example of how to check traces properties in the evaluator.
run {
    all b : Board | wellformed[b]
    traces
} for exactly 10 Board, exactly 3 Boat, exactly 6 BoatSpot, exactly 3 MissedStrike for {next is linear}
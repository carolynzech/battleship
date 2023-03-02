#lang forge "curiosity modeling" "le4s1dpsmgywfv79@gmail.com"

abstract sig Boolean {}
one sig True, False extends Boolean {}

one sig Game {
   initial: one Board,
   next: pfunc Board -> Board
}

abstract sig Space {}

sig BoatSpot extends Space {}

sig MissedStrike extends Space {}

sig Boat {
    spot1: one BoatSpot,
    spot2: one BoatSpot
}

sig Board {
    board: pfunc Int -> Int -> Space,
    boats: set Boat,
    hit_boatspots: func BoatSpot -> Boolean,
    has_lost: one Boolean
}

pred wellformed[b: Board] {

    // each board has three boats
    #{boat: Boat | boat in b.boats} = 3
    
    // check for valid dimensions
    all row, col : Int | {
        (row < 0 or col < 0 or row > 5 or col > 5) implies (no b.board[row][col])
    }

    all space: Space | {
        all row, col, row2, col2 : Int | (row != row2 or col != col2) implies {
            // the space can't show up more than once on a given player's board
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

        // BoatSpots of this Boat are positioned vertically or horizontally -- no diagonal
        all row, col: Int | (b.board[row][col] = boat.spot1) implies {
            (b.board[row][add[col,1]] = boat.spot2 or b.board[row][add[col,-1]] = boat.spot2 or b.board[add[row,1]][col] = boat.spot2 or b.board[add[row,-1]][col] = boat.spot2)
        }
    }
    b.has_lost = True iff final[b]
}

pred init[b: Board] {
    // no MissedStrikes on initial board
    all row, col : Int | {
        no ms : MissedStrike | {
            b.board[row][col] = ms
        }
    }

    // no BoatSpots are hit
    // all BoatSpots must be present on the initial board. This contraint, combined with the constraints in 
    // move and doNothing about the board, ensures that every boatspot is present in the same spot on every board
    all spot : BoatSpot | {
        some row, col : Int | {
            b.board[row][col] = spot
            b.board[row][col] = spot implies b.hit_boatspots[spot]= False
        }
    }
    // player hasn't lost
    b.has_lost = False
}

// This is true when Board has lost the game
pred final[b: Board] {
    // all boat spots on Board's board are hit
    all spot : BoatSpot | {
        all row, col : Int | (b.board[row][col] = spot) implies {
            b.hit_boatspots[spot] = True
        }
    }
}

// Checks that (row, col) is a valid spot for a move on Board b
// A spot is valid if it is on the board and if it contains 1) an empty space or 2) a BoatSpot that has not yet been hit
pred validLocation[row: Int, col: Int, b: Board] {
    // on board
    (row >= 0 and col >= 0 and row <= 5 and col <= 5)
    // either empty or boat spot that isn't hit
    (no b.board[row][col]) or (some spot: BoatSpot | (b.board[row][col] = spot and b.hit_boatspots[spot] = False))
}

pred move[pre: Board, post: Board, row: Int, col: Int] {

    // GUARD
    validLocation[row, col, pre]
    not final[pre]

    // ACTION

    // If the place we're moving is a boatspot:
    some pre.board[row][col] implies {
        post.board[row][col] = pre.board[row][col] // boatspot remains in place
        pre.hit_boatspots[pre.board[row][col]] = False
        post.hit_boatspots[post.board[row][col]] = True // set hit to true
    } else {
        // if striking empty location, insert a MissedStrike on the board
        some ms : MissedStrike | {
            post.board[row][col] = ms
        }
        pre.hit_boatspots = post.hit_boatspots // no boatspot should be hit
    }

    // MAINTAIN PREVIOUS/UNINVOLVED fields

    // either one boatspot is hit (board[row][col] is a boatspot) or none are (board[row][col] is an empty space)
    // since we check that there's no change for the empty space case, this is really just a fast way to check that
    // only one boatspot was hit during the move without having to loop over all other row, col
    #{spot : BoatSpot | pre.hit_boatspots[spot] != post.hit_boatspots[spot]} <= 1

    // all other spaces on the board stays the same
    all row2, col2 : Int | (row != row2 or col != col2) implies {
        post.board[row2][col2] = pre.board[row2][col2]
    }
}

pred doNothing[pre: Board, post: Board] {
    -- GUARD
    pre.has_lost = True

    -- ACTION
    all row, col: Int | 
        post.board[row][col] = pre.board[row][col]
    
    #{spot : BoatSpot | pre.hit_boatspots[spot] != post.hit_boatspots[spot]} = 0
    post.has_lost = True

}

pred traces {
    init[Game.initial]
    // all states are reachable through next from the initial state except the initial state
    // and the initial state is not reachable from anything
    // every board except initial itself is reachable from initial, forcing initial to be the first board
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

run {
    all b : Board | wellformed[b]
    traces
} for exactly 4 Board, exactly 3 Boat, exactly 6 BoatSpot, exactly 1 MissedStrike for {next is linear}
#lang forge "curiosity modeling" "le4s1dpsmgywfv79@gmail.com"

abstract sig Boolean {}
one sig True, False extends Boolean {}

// whether we should have actual defined empty space that extends space
// he thinks that the adjacency checking isn't working

one sig Game {
   initial: one Board,
   // make both of these {next is linear}, don't use and just new line to separate them
   next: pfunc Board -> Board
}

abstract sig Space {}

sig BoatSpot extends Space {
    hit: one Boolean
}

sig MissedStrike extends Space {}

sig Boat {
    spot1: one BoatSpot,
    spot2: one BoatSpot
}

sig Board {
    board: pfunc Int -> Int -> Space,
    // boat1: one Boat,
    // boat2: one Boat,
    // boat3: one Boat,
    boats: set Boat,
    // if we have performance difficulties, it's possible that there's overhead with keeping the boards synced -- seek advice!
    has_lost: one Boolean
}

// to decide whose turn it is, need to count MissedStrikes and hit BoatSpots

pred wellformed[b: Board] {
    // each board has three boats
    #{boat: Boat | boat in b.boats} = 3
    // check for valid dimensions
    all row, col : Int | {
        (row < 0 or col < 0 or row > 3 or col > 3) implies (no b.board[row][col])
    }

    all space: Space | {
        // if a space object exists, it must be on a board
        some row, col: Int | {
            b.board[row][col] = space
        }

        all row, col, row2, col2 : Int | (row != row2 or col != col2) implies {
            b.board[row][col] = space implies {
                // the space can't show up more than once on a given player's board
                (b.board[row2][col2] != space)
            }
        }
    }

    // each BoatSpot belongs to only 1 boat
    all boat: Boat | {
        // spot at spot1 can't be the same as spot at spot2
        boat.spot1 != boat.spot2
        // spot belonging to one boat can't belong to any other boat
        all boat2: Boat | boat2 != boat implies {
            boat.spot1 != boat2.spot1
            boat.spot1 != boat2.spot2
            boat.spot2 != boat2.spot2
            boat.spot2 != boat2.spot1
        }
        // BoatSpots of this Boat are positioned vertically or horizontally -- no diagonal
        all row, col: Int | (b.board[row][col] = boat.spot1) implies {
            (b.board[row][add[col,1]] = boat.spot2 or b.board[row][add[col,-1]] = boat.spot2 or b.board[add[row,1]][col] = boat.spot2 or b.board[add[row,-1]][col] = boat.spot2)
        }
    }
}

pred init[b: Board] {
    // only boat spots that aren't hit, no strikes
    no row, col : Int | {
        b.board[row][col] = MissedStrike 
    }

    all spot : BoatSpot | {
        some row, col : Int | b.board[row][col] = spot implies {
            spot.hit = False
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
            spot.hit = True
        }
    }
}

// checks that for the selected row, col, and board, the move is valid
pred validLocation[row: Int, col: Int, b: Board] {
    // on board
    (row >= 0 and col >= 0 and row <= 3 and col <= 3)
    // either empty or boat spot that isn't hit
    (no b.board[row][col]) or (some spot: BoatSpot | (b.board[row][col] = spot and spot.hit = False))
}

pred move[pre: Board, post: Board, row: Int, col: Int] {

    // GUARD
    // pre board isn't final state
    not final[pre]
    
    // valid location for move
    validLocation[row, col, pre]

    // ACTION
    // if boat spot: 
    some spot: BoatSpot | pre.board[row][col] = spot implies {
        post.board[row][col] = spot
        spot.hit = True
    }
    // if empty location:
    no pre.board[row][col] implies {
        post.board[row][col] = MissedStrike
    }

    // if final state, Player has lost
    final[post] implies {
        post.has_lost = True
    }
}

pred traces {
    // wellformed

    // init[Game.initial1]
    // init[Game.initial2]
    // all b1, b2: Board | some (Game.next1[b1] and Game.next2[b2]) implies {
    //     some row, col: Int, p: Board | {
    //         move[b, Game.next[b], row, col, p]            
    //     }
    //     or
    //         doNothing[b, Game.next[b]]
    // }


}

run {
    all b: Board | wellformed[b]
} for exactly 2 Board, exactly 3 Boat, exactly 6 BoatSpot, 5 Int
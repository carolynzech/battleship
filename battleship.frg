#lang forge/bsl "curiosity modeling" "le4s1dpsmgywfv79@gmail.com"

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig Game {
   initial1: one Board,
   initial2: one Board,
   // make both of these {next is linear}, don't use and just new line to separate them
   next1: pfunc Board -> Board,
   next2: pfunc Board -> Board,
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

abstract sig Board {
    board: pfunc Int -> Int -> Space
    boat1: one Boat,
    boat2: one Boat,
    boat3: one Boat,
    // if we have performance difficulties, it's possible that there's overhead with keeping the boards synced -- seek advice!
    my_turn: one Boolean,
    has_won: one Boolean
}

one sig Board1, Board2 extends Board {}

// to decide whose turn it is, need to count MissedStrikes and hit BoatSpots

pred wellformed {
    // two players (????)
    // dimensions of each board
    all board: Board | {
        all row, col : Int | {
            (row < 0 or col < 0 or row > 4 or col > 4) implies no board.board[row][col]
        }
        // positions of boats on board
        some row,col: Int | {
            #{spot: BoatSpot | board.board[row][col] = spot} = 6
        }    
        // next to each other (vertical or horizontal - no diagonal)
        // all boat: Boat | {
        //     some row, col: Int | {
        //         b
        //     }
        // }    
    }
    

    
    // 3 boats each player


}

pred initState {
    // only boat spots that aren't hit, no strikes
    // no one has won
    // its one player's turn
}

pred finalState[p: Player] {
    // all boat spots on player's board are hit
}

// pred changeTurn {

// }

pred validSpot[row: Int, col: Int, board: Board] {
    // on board
    // either empty or boat spot that isn't hit
}

pred move[pre1: Board, post1: Board, pre2: Board, post2: Board, row: Int, col: Int] {

    // guard: neither board is in final state
    // should wellformed be part of the guard?
    
    // if board1's turn:
        // if validSpot[row, col, board2]:
            // if boat spot: 
                // post2[row][col].hit = 1
            // if nothing:
                // post2[row][col] = MissedStrike
        // post1 = pre1 // only one board changes at a time

    // same for board2

    // if finalState of board1: set board2 has_won to 1
    // if finalState of board2: set board1 has_won to 1

    // if it was board1's turn, it's board2's
    // vice versa
}

pred traces {
    // init[Game.initial1]
    // init[Game.initial2]
    // all b1, b2: Board | some (Game.next1[b1] and Game.next2[b2]) implies {
    //     some row, col: Int, p: Player | {
    //         move[b, Game.next[b], row, col, p]            
    //     }
    //     or
    //         doNothing[b, Game.next[b]]
    // }


}
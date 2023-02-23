#lang forge/bsl "curiosity modeling" "le4s1dpsmgywfv79@gmail.com"

sig Game {
   initial1: one Board,
   initial2: one Board,
   next1: pfunc Board -> Board,
   next2: pfunc Board -> Board,
}

abstract sig Space {}

sig BoatSpot extends Space {
    hit: lone Int
}

sig MissedStrike extends Space {}

sig Boat {
    spot1: lone BoatSpot,
    spot2: lone BoatSpot
}

abstract sig Board {
    board: pfunc Int -> Int -> Space
    boat1: one Boat,
    boat2: one Boat,
    boat3: one Boat,
    my_turn: lone Int
    has_won: lone Int
}

one sig Board1, Board2 extends Board {}

// to decide whose turn it is, need to count MissedStrikes and hit BoatSpots

pred wellformed {
    // two players
    // dimensions of each board
    // positions of boats on board & next to each other (vertical or horizontal - no diagonal)
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

// ?????
pred traces {

}
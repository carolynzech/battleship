#lang forge "curiosity modeling" "le4s1dpsmgywfv79@gmail.com"

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig Game {
   initial1: one Player,
   initial2: one Player,
   // make both of these {next is linear}, don't use and just new line to separate them
   next1: pfunc Player -> Player,
   next2: pfunc Player -> Player
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

abstract sig Player {
    board: pfunc Int -> Int -> Space,
    // boat1: one Boat,
    // boat2: one Boat,
    // boat3: one Boat,
    boats: set Boat,
    // if we have performance difficulties, it's possible that there's overhead with keeping the boards synced -- seek advice!
    my_turn: one Boolean,
    has_won: one Boolean
}

one sig Player1, Player2 extends Player {}

// to decide whose turn it is, need to count MissedStrikes and hit BoatSpots

pred wellformed {
    // two players (????)
    // #{p: Player | 1=1} = 2
    some Player1
    some Player2
    #{p: Player | p != Player1 and p!= Player2} = 0
    #{boat: Boat | boat in Player1.boats} = 3
    #{boat: Boat | boat in Player2.boats} = 3

    
    // dimensions of each board
    all row, col : Int | {
        (row < 0 or col < 0 or row > 4 or col > 4) implies (no Player1.board[row][col] and no Player2.board[row][col])
    }
    // positions of boats on board

    
    all space: Space | {
        // the space can't show up on more than once on a given player's board
        // this works!!
        all player : Player | {
            one row,col : Int | {
                player.board[row][col] = space
            }
            some row, col: Int | (player.board[row][col] = space) implies {
                all player2 : Player | player != player2 implies {
                    all row2, col2 : Int | {
                        player2.board[row2][col2] != space
                    }
                    
                }
            }
        }

        // some row, col : Int | (Player1.board[row][col] = space) implies {
        //     Player2.board[row][col] != space
        // }

        // some row, col : Int | (Player2.board[row][col] = space) implies {
        //     Player1.board[row][col] != space
        // }

        // one row, col : Int | {
        //     // xor
        //     (Player1.board[row][col] = space and not Player2.board[row][col] = space) or (not Player1.board[row][col] = space and Player2.board[row][col] = space)
        // }
    }
    
    

    // each space either has one spot or none

    // each BoatSpot belongs to only 1 boat
    all boat: Boat | {
        // spot at spot1 can't be the same as spot at spot2
        boat.spot1 != boat.spot2
        // spot belonging to one boat can't belong to any other boat
        // all boat2: Boat | boat2 != boat implies {
        //     boat.spot1 != boat2.spot1
        //     boat.spot1 != boat2.spot2
        //     boat.spot2 != boat2.spot2
        //     boat.spot2 != boat2.spot1
        // }
        
    }

    // there can't be more than one spot per space
    // this spot can't be anywhere else on this players board
    // this spot can't be on the other player's board
    
    // next to each other (vertical or horizontal - no diagonal)
    // all boat: Boat | {
    //     some row, col: Int | {
    //         player.board[row][col] = boat.spot1 implies (player.board[row][add[col,1]] = boat.spot2 or player.board[row][add[col,-1]] = boat.spot2 or player.board[add[row,1]][col] = boat.spot2 or player.board[add[row,-1]][col] = boat.spot2)
    //     }

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

pred validSpot[row: Int, col: Int, board: Player] {
    // on board
    // either empty or boat spot that isn't hit
}

pred move[pre1: Player, post1: Player, pre2: Player, post2: Player, row: Int, col: Int] {

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
    // all b1, b2: Player | some (Game.next1[b1] and Game.next2[b2]) implies {
    //     some row, col: Int, p: Player | {
    //         move[b, Game.next[b], row, col, p]            
    //     }
    //     or
    //         doNothing[b, Game.next[b]]
    // }


}

run {wellformed} for exactly 2 Player
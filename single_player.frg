#lang forge "curiosity modeling" "le4s1dpsmgywfv79@gmail.com"

abstract sig Boolean {}
one sig True, False extends Boolean {}

// whether we should have actual defined empty space that extends space
// he thinks that the adjacency checking isn't working

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
    some Player1
    some Player2
    #{p: Player | p != Player1 and p!= Player2} = 0
    #{boat: Boat | boat in Player1.boats} = 3
    #{boat: Boat | boat in Player2.boats} = 3
    #{Player1.boats & Player2.boats} = 0

    // dimensions of each board
    all row, col : Int | {
        (row < 0 or col < 0 or row > 3 or col > 3) implies (no Player1.board[row][col] and no Player2.board[row][col])
    }
    
    all space: Space | {

        // if a space object exists, it must be on a board
        some player : Player | {
            some row, col: Int | {
                player.board[row][col] = space
            }
        }

        all row, col, row2, col2 : Int | (row != row2 or col != col2) implies {
                Player1.board[row][col] = space implies {
                    // the space can't show up more than once on a given player's board
                    (Player1.board[row2][col2] != space)
                    // the other player's board cannot contain the space
                    Player2.board[row][col] != space
                    Player2.board[row2][col2] != space
                }
                Player2.board[row][col] = space implies {
                    // the space can't show up more than once on a given player's board
                    (Player2.board[row2][col2] != space)
                    // the other player's board cannot contain the space
                    Player1.board[row][col] != space
                    Player1.board[row2][col2] != space
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
        some row, col: Int | {
            Player1.board[row][col] = boat.spot1 implies (Player1.board[row][add[col,1]] = boat.spot2 or Player1.board[row][add[col,-1]] = boat.spot2 or Player1.board[add[row,1]][col] = boat.spot2 or Player1.board[add[row,-1]][col] = boat.spot2)
            Player2.board[row][col] = boat.spot1 implies (Player2.board[row][add[col,1]] = boat.spot2 or Player2.board[row][add[col,-1]] = boat.spot2 or Player2.board[add[row,1]][col] = boat.spot2 or Player2.board[add[row,-1]][col] = boat.spot2)
        }
    }
}

pred initState {
    // only boat spots that aren't hit, no strikes
    no MissedStrike

    all spot : BoatSpot | {
        spot.hit = False
    }
    // no one has won
    Player1.has_won = False
    Player2.has_won = False
    
    // it's exactly one player's turn
    (Player1.my_turn = True and Player2.my_turn = False) or (Player1.my_turn = False and Player2.my_turn = True)
}

// This is true when p has lost the game
pred finalState[p: Player] {
    // all boat spots on player's board are hit
    all spot : BoatSpot | {
        some row, col : Int | {p.board[row][col] = spot} implies {
            spot.hit = True
        }
    }
}

// pred changeTurn {

// }

// checks that the selected row, col for the move is valid
pred validLocation[row: Int, col: Int, p: Player] {
    // on board
    (row >= 0 and col >= 0 and row <= 3 and col <= 3)
    // either empty or boat spot that isn't hit
    (no p.board[row][col]) or (some spot: BoatSpot | (p.board[row][col] = spot and spot.hit = False))
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

run {validLocation[2, 2, Player1] wellformed} for exactly 2 Player, exactly 6 Boat, exactly 12 BoatSpot, 5 Int
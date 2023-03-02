#lang forge "curiosity modeling tests" "le4s1dpsmgywfv79@gmail.com"

open "battleship.frg"

// Tests for each predicate

// * note for carolyn: we should make a theorem/sat test that shows you can move anywhere on an init board (to a wellformed board) *

test suite for wellformed {
    // board with all reqs
    example goodBoard is {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
    }
    // board with extra boat & boat spots
    example wrongNumBoats is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2 + `Boat3
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5 + `BoatSpot6 + `BoatSpot7
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4 + `Boat3 -> `BoatSpot6
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5 + `Boat3 -> `BoatSpot7
    }
    // board with Space outside board dimensions
    example invalidDimensions is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> -1 -> `BoatSpot1
    }
    // no neighboring sister spot for the spot1 places
    example lonelySpot is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        board = `Board0 -> 4 -> 1 -> `BoatSpot0
    }
    // same space shows up more than once on board
    example duplicateSpace is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        board = `Board0 -> 4 -> 1 -> `BoatSpot0 +
                `Board0 -> 4 -> 2 -> `BoatSpot0
    }
    // one Boat has the same BoatSpot for spot1 and spot2
    example duplicateBoatSpot is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
    }
    // two Boat have the same BoatSpot as a part of their boat
    example sharingBoatSpot is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot1 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
    }
    // spot1 and spot2 of a boat are placed on board diagonally instead of horizontally/vertically
    example diagonalBoat is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        board = `Board0 -> 1 -> 1 -> `BoatSpot0 +
                `Board0 -> 2 -> 2 -> `BoatSpot1
    }
    // board has lost even though the board is not at a final state - not all BoatSpots are hit
    example falseLoss is not {some b: Board | wellformed[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `True +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `False
        has_lost = `Board0 -> `True
    }
}

test suite for init {
    // init board with all reqs
    example goodInit is {some b: Board | init[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `False + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False
        has_lost = `Board0 -> `False
    }
    // missed strike on init board
    example missedStrikeInit is not {some b: Board | init[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5 + `MissedStrike0
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `False + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False
        board = `Board0 -> 1 -> 1 -> `MissedStrike0
        has_lost = `Board0 -> `False
    }
    // one BoatSpot hit on init board
    example hitSpotInit is not {some b: Board | init[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `False + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `True
        has_lost = `Board0 -> `False
    }
    // has_lost is True for init board
    example hasLostInit is not {some b: Board | init[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `False + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False
        has_lost = `Board0 -> `True
    }
}

test suite for final {
    // final board with all reqs
    example goodFinal is {some b: Board | final[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `True +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `True
    }
    // final board with one BoardSpot not hit
    example notAllHit is not {some b: Board | final[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `True +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `False
    }
    // final board with all unhit BoatSpots
    example noneHit is not {some b: Board | final[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `False + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False
    }
}

test suite for validLocation {
    // valid location for the given board - unhit BoatSpot
    example goodUnhitSpot is {some b: Board | validLocation[0,0,b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `False + 
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `False
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5
    }
    // valid location for the given board - empty location
    example goodEmptyLoc is {some b: Board | validLocation[0,0,b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        board = `Board0 -> 1 -> 1 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5
    }
    // invalid location because outside bounds of board
    example locationNotOnBoard is not {some b: Board | validLocation[-1,0,b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
    }
    // invalid location because there is a MissedStrike at the location
    example missedStrikeAtLoc is not {some b: Board | validLocation[0,0,b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5 + `MissedStrike0
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        board = `Board0 -> 1 -> 1 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board0 -> 0 -> 0 -> `MissedStrike0
    } -- note for carolyn: this passes without the "not" too :(
    // invalid location because there is a hit BoatSpot at the location
    example hitBoatSpotAtLoc is not {some b: Board | validLocation[0,0,b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `False
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5
    }
}

test suite for move {
    // note for carolyn: we def don't have to do all of these also i can do some tomorrow :)
    // trying to move at an invalid location - 3 options: off the board, missed strike, hit boatspot (but we already test for these 3 in test suite for validLoc)
    // trying to move on a board that has already lost (pre is final)
    // move on at location of a boatspot but post's corresponding boatspot isn't hit
    // move on at location of a boatspot and boatspot's location changes in post
    // move on at empty location but no missedstrike is added to post at that loc
    // move on at empty location and hit_boatspots changes
    // more than one boatspot changes to hit
    // other spaces on the board change
}

test suite for doNothing {
    // should do nothing between given boards
    example goodDoNothing is {some pre, post: Board | doNothing[pre, post]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        has_lost = `Board0 -> `True + `Board1 -> `True
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `True +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `True +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `True +
                        `Board1 -> `BoatSpot2 -> `True +
                        `Board1 -> `BoatSpot3 -> `True +
                        `Board1 -> `BoatSpot4 -> `True +
                        `Board1 -> `BoatSpot5 -> `True
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board1 -> 0 -> 0 -> `BoatSpot0 +
                `Board1 -> 0 -> 1 -> `BoatSpot1 + 
                `Board1 -> 2 -> 2 -> `BoatSpot2 + 
                `Board1 -> 2 -> 3 -> `BoatSpot3 + 
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    }
    // pre board that hasn't lost yet
    example hasntLost is not {some pre, post: Board | doNothing[pre, post]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        has_lost = `Board0 -> `False + `Board1 -> `False
    }
    // not every row,col in pre matches row,col in post
    example boardChanges is not {some pre, post: Board | pre!= post and doNothing[pre, post]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        has_lost = `Board0 -> `True + `Board1 -> `True
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `True +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `True +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `True +
                        `Board1 -> `BoatSpot2 -> `True +
                        `Board1 -> `BoatSpot3 -> `True +
                        `Board1 -> `BoatSpot4 -> `True +
                        `Board1 -> `BoatSpot5 -> `True
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                -- these next two row, col are different from...
                `Board0 -> 1 -> 1 -> `BoatSpot4 + 
                `Board0 -> 1 -> 2 -> `BoatSpot5 +
                `Board1 -> 0 -> 0 -> `BoatSpot0 +
                `Board1 -> 0 -> 1 -> `BoatSpot1 + 
                `Board1 -> 2 -> 2 -> `BoatSpot2 + 
                `Board1 -> 2 -> 3 -> `BoatSpot3 + 
                -- ... these! so it should fail because it surely did not do nothing smh
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    } -- note for carolyn: had to add pre!= post to these otherwise they put in two of the same board which always passed, don't know if
    -- we want to add that to doNothing so that you can't pass in two of the same board
    // the boatspots change between pre and post
    example hitsChange is not {some pre, post: Board | pre!= post and doNothing[pre, post]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        has_lost = `Board0 -> `True + `Board1 -> `True
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        -- BoatSpot1 is hit here ...
                        `Board0 -> `BoatSpot1 -> `True +
                        `Board0 -> `BoatSpot2 -> `True +
                        `Board0 -> `BoatSpot3 -> `True +
                        `Board0 -> `BoatSpot4 -> `True +
                        `Board0 -> `BoatSpot5 -> `True +
                        `Board1 -> `BoatSpot0 -> `True + 
                        -- ... but not here! bad doNothing
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `True +
                        `Board1 -> `BoatSpot3 -> `True +
                        `Board1 -> `BoatSpot4 -> `True +
                        `Board1 -> `BoatSpot5 -> `True
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board1 -> 0 -> 0 -> `BoatSpot0 +
                `Board1 -> 0 -> 1 -> `BoatSpot1 + 
                `Board1 -> 2 -> 2 -> `BoatSpot2 + 
                `Board1 -> 2 -> 3 -> `BoatSpot3 + 
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    } -- note for carolyn: same as above
    // pre has lost but post hasn't
    example lostChanges is not {some pre, post: Board | pre != post and doNothing[pre, post]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        has_lost = `Board0 -> `False + `Board1 -> `True
    } -- note for carolyn: same as above
}

test suite for traces {
    // everything looks good yay
    example goodTraces is traces for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1 + `Board2
        initial = `Game0 -> `Board0
        next = `Game0 -> `Board0 -> `Board1 + `Game0 -> `Board1 -> `Board2 + `Game0 -> `Board2 -> none
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        has_lost = `Board0 -> `False + `Board1 -> `False + `Board2 -> `True
    } -- note for carolyn: when i make board2 haslost False i feel like it should fail because board2's next 
    -- is none but it passes... idk if that's a problem/something we need to test
    // initial board doesn't pass init - theres a MissedStrike on the board
    example badInitial is not traces for {   
        Game = `Game0
        Board = `Board0
        initial = `Game0 -> `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5 + `MissedStrike0
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board0 -> 1 -> 1 -> `MissedStrike0
    } -- note for carolyn: this passes when you remove "not" too
    // intial isn't actually the first board (some other board points to initial)
    example initialNotFirst is not traces for {   
        Game = `Game0
        Board = `Board0 + `Board1
        initial = `Game0 -> `Board0
        next = `Game0 -> `Board1 -> `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        Space = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
    }
    // note for carolyn: not really sure how to/if we should test the last part of traces
}

// should have some sat/unsat tests, and maybe theorem tests too, for the predicates working together
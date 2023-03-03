#lang forge "curiosity modeling tests" "le4s1dpsmgywfv79@gmail.com"

open "battleship.frg"

// Tests for each predicate

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
    }
    // missed strike on init board
    example missedStrikeInit is not {some b: Board | init[b]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        BoatSpot = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        MissedStrike = `MissedStrike0
        Space = BoatSpot + MissedStrike
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
        BoatSpot = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        MissedStrike = `MissedStrike0
        Space = BoatSpot + MissedStrike
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
    }
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
    
    // move on boatspot and it's marked as hit in the post state
    example boatHit is {some pre, post: Board | move[pre, post, 2, 2]} for {   
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
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `True +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `False
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

    // move on at empty location and missedstrike is added to post at that loc
    example moveOnEmpty is {some pre, post: Board | move[pre, post, 2, 4]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        BoatSpot = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        MissedStrike = `MissedStrike0
        Space = BoatSpot + MissedStrike
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `False
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
                `Board1 -> 2 -> 4 -> `MissedStrike0 +
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    }

    // trying to move on a board that has already lost (pre is final)
    example haveLost is not {some pre, post: Board | move[pre, post, 2, 2]} for {   
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

    // move on at location of a boatspot but post's corresponding boatspot isn't hit
    example boatNotHit is not {some pre, post: Board | move[pre, post, 2, 2]} for {   
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
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False + // this should be True
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `False
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

    // move on at location of a boatspot and boatspot's location changes in post
    example teleportingBoatSpot is not {some pre, post: Board | move[pre, post, 2, 2]} for {   
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
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `True +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `False
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board1 -> 0 -> 0 -> `BoatSpot0 +
                `Board1 -> 0 -> 1 -> `BoatSpot1 + 
                `Board1 -> 2 -> 4 -> `BoatSpot2 + // teleported from (2, 2) to (2, 4)
                `Board1 -> 2 -> 3 -> `BoatSpot3 + 
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    }

    // move on at empty location but missedstrike is not added to post at that loc
    example noMissedStrikeOnMove is not {some pre, post: Board | move[pre, post, 2, 4]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        BoatSpot = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        MissedStrike = `MissedStrike0
        Space = BoatSpot + MissedStrike
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `False
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board1 -> 0 -> 0 -> `BoatSpot0 +
                `Board1 -> 0 -> 1 -> `BoatSpot1 + 
                // should be a MissedStrike at (2, 4)
                `Board1 -> 2 -> 2 -> `BoatSpot2 +
                `Board1 -> 2 -> 3 -> `BoatSpot3 + 
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    }

    // move on at empty location and hit_boatspots changes
    example hitBoatSpotsChangeOnEmpty is not {some pre, post: Board | move[pre, post, 2, 4]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        BoatSpot = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        MissedStrike = `MissedStrike0
        Space = BoatSpot + MissedStrike
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `True // this should have stayed False
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board1 -> 0 -> 0 -> `BoatSpot0 +
                `Board1 -> 0 -> 1 -> `BoatSpot1 + 
                `Board1 -> 2 -> 4 -> `MissedStrike0 +
                `Board1 -> 2 -> 2 -> `BoatSpot2 +
                `Board1 -> 2 -> 3 -> `BoatSpot3 + 
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    }

    // more than one boatspot changes to hit
    example multipleBoatsHit is not {some pre, post: Board | move[pre, post, 2, 2]} for {   
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
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `True // this should have stayed False
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

    // other spaces on the board change
    example unrelatedSpacesChange is not {some pre, post: Board | move[pre, post, 2, 4]} for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1
        Boat = `Boat0 + `Boat1 + `Boat2
        BoatSpot = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        MissedStrike = `MissedStrike0
        Space = BoatSpot + MissedStrike
        boats = `Board0 -> {`Boat0 + `Boat1 + `Boat2} + `Board1 -> {`Boat0 + `Boat1 + `Boat2}
        spot1 = `Boat0 -> `BoatSpot0 + `Boat1 -> `BoatSpot2 + `Boat2 -> `BoatSpot4
        spot2 = `Boat0 -> `BoatSpot1 + `Boat1 -> `BoatSpot3 + `Boat2 -> `BoatSpot5
        hit_boatspots = `Board0 -> `BoatSpot0 -> `True + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `True + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `True +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `False
        board = `Board0 -> 0 -> 0 -> `BoatSpot0 +
                `Board0 -> 0 -> 1 -> `BoatSpot1 + 
                `Board0 -> 2 -> 2 -> `BoatSpot2 + 
                `Board0 -> 2 -> 3 -> `BoatSpot3 + 
                `Board0 -> 4 -> 4 -> `BoatSpot4 + 
                `Board0 -> 3 -> 4 -> `BoatSpot5 +
                `Board1 -> 0 -> 0 -> `BoatSpot0 +
                `Board1 -> 0 -> 1 -> `BoatSpot1 + 
                `Board1 -> 2 -> 4 -> `MissedStrike0 +
                `Board1 -> 2 -> 5 -> `BoatSpot2 + // this BoatSpot moves from (2, 2) to (2, 5)
                `Board1 -> 2 -> 3 -> `BoatSpot3 + 
                `Board1 -> 4 -> 4 -> `BoatSpot4 + 
                `Board1 -> 3 -> 4 -> `BoatSpot5
    }

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
        hit_boatspots = `Board0 -> `BoatSpot0 -> `False + 
                        `Board0 -> `BoatSpot1 -> `False +
                        `Board0 -> `BoatSpot2 -> `False +
                        `Board0 -> `BoatSpot3 -> `False +
                        `Board0 -> `BoatSpot4 -> `False +
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `False + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `True
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
    }
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
    }
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
                        // post has one boatspot left to be hit
                        `Board1 -> `BoatSpot5 -> `False
    }
}

test suite for traces {
    // everything looks good yay
    example goodTraces is traces for {   
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1 + `Board2 + `Board3 + `Board4 + `Board5 + `Board6
        initial = `Game0 -> `Board0
        next = `Game0 -> `Board0 -> `Board1 + `Game0 -> `Board1 -> `Board2 + `Game0 -> `Board2 -> `Board3 + `Game0 -> `Board3 -> `Board4 + `Game0 -> `Board4 -> `Board5 + `Game0 -> `Board5 -> `Board6 + `Game0 -> `Board6 -> none
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
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `False + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `True +
                        `Board2 -> `BoatSpot0 -> `False + 
                        `Board2 -> `BoatSpot1 -> `False +
                        `Board2 -> `BoatSpot2 -> `False +
                        `Board2 -> `BoatSpot3 -> `False +
                        `Board2 -> `BoatSpot4 -> `True +
                        `Board2 -> `BoatSpot5 -> `True +
                        `Board3 -> `BoatSpot0 -> `False + 
                        `Board3 -> `BoatSpot1 -> `False +
                        `Board3 -> `BoatSpot2 -> `False +
                        `Board3 -> `BoatSpot3 -> `True +
                        `Board3 -> `BoatSpot4 -> `True +
                        `Board3 -> `BoatSpot5 -> `True +
                        `Board4 -> `BoatSpot0 -> `False + 
                        `Board4 -> `BoatSpot1 -> `False +
                        `Board4 -> `BoatSpot2 -> `True +
                        `Board4 -> `BoatSpot3 -> `True +
                        `Board4 -> `BoatSpot4 -> `True +
                        `Board4 -> `BoatSpot5 -> `True +
                        `Board5 -> `BoatSpot0 -> `False + 
                        `Board5 -> `BoatSpot1 -> `True +
                        `Board5 -> `BoatSpot2 -> `True +
                        `Board5 -> `BoatSpot3 -> `True +
                        `Board5 -> `BoatSpot4 -> `True +
                        `Board5 -> `BoatSpot5 -> `True +
                        `Board6 -> `BoatSpot0 -> `True + 
                        `Board6 -> `BoatSpot1 -> `True +
                        `Board6 -> `BoatSpot2 -> `True +
                        `Board6 -> `BoatSpot3 -> `True +
                        `Board6 -> `BoatSpot4 -> `True +
                        `Board6 -> `BoatSpot5 -> `True
    }
    // initial board doesn't pass init - theres a MissedStrike on the board
    example badInitial is not traces for {   
        Game = `Game0
        Board = `Board0
        initial = `Game0 -> `Board0
        Boat = `Boat0 + `Boat1 + `Boat2
        BoatSpot = `BoatSpot0 + `BoatSpot1 + `BoatSpot2 + `BoatSpot3 + `BoatSpot4 + `BoatSpot5
        MissedStrike = `MissedStrike0
        Space = BoatSpot + MissedStrike
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
    }
    // // initial isn't actually the first board (some other board points to initial)
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

    // same as goodTraces, but the last board has not yet lost
    example doesntEndOnFinal is not traces for {
        Game = `Game0
        Boolean = `True + `False
        True = `True
        False = `False
        Board = `Board0 + `Board1 + `Board2 + `Board3 + `Board4 + `Board5 + `Board6
        initial = `Game0 -> `Board0
        next = `Game0 -> `Board0 -> `Board1 + `Game0 -> `Board1 -> `Board2 + `Game0 -> `Board2 -> `Board3 + `Game0 -> `Board3 -> `Board4 + `Game0 -> `Board4 -> `Board5 + `Game0 -> `Board5 -> `Board6 + `Game0 -> `Board6 -> none
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
                        `Board0 -> `BoatSpot5 -> `False +
                        `Board1 -> `BoatSpot0 -> `False + 
                        `Board1 -> `BoatSpot1 -> `False +
                        `Board1 -> `BoatSpot2 -> `False +
                        `Board1 -> `BoatSpot3 -> `False +
                        `Board1 -> `BoatSpot4 -> `False +
                        `Board1 -> `BoatSpot5 -> `True +
                        `Board2 -> `BoatSpot0 -> `False + 
                        `Board2 -> `BoatSpot1 -> `False +
                        `Board2 -> `BoatSpot2 -> `False +
                        `Board2 -> `BoatSpot3 -> `False +
                        `Board2 -> `BoatSpot4 -> `True +
                        `Board2 -> `BoatSpot5 -> `True +
                        `Board3 -> `BoatSpot0 -> `False + 
                        `Board3 -> `BoatSpot1 -> `False +
                        `Board3 -> `BoatSpot2 -> `False +
                        `Board3 -> `BoatSpot3 -> `True +
                        `Board3 -> `BoatSpot4 -> `True +
                        `Board3 -> `BoatSpot5 -> `True +
                        `Board4 -> `BoatSpot0 -> `False + 
                        `Board4 -> `BoatSpot1 -> `False +
                        `Board4 -> `BoatSpot2 -> `True +
                        `Board4 -> `BoatSpot3 -> `True +
                        `Board4 -> `BoatSpot4 -> `True +
                        `Board4 -> `BoatSpot5 -> `True +
                        `Board5 -> `BoatSpot0 -> `False + 
                        `Board5 -> `BoatSpot1 -> `True +
                        `Board5 -> `BoatSpot2 -> `True +
                        `Board5 -> `BoatSpot3 -> `True +
                        `Board5 -> `BoatSpot4 -> `True +
                        `Board5 -> `BoatSpot5 -> `True +
                        `Board6 -> `BoatSpot0 -> `True + 
                        `Board6 -> `BoatSpot1 -> `True +
                        `Board6 -> `BoatSpot2 -> `True +
                        `Board6 -> `BoatSpot3 -> `True +
                        `Board6 -> `BoatSpot4 -> `True +
                        // haven't lost yet
                        `Board6 -> `BoatSpot5 -> `False
    }
}

// Verifying some interesting properties about our model
test expect {
    // need traces of at least length 7 is unsat minimum 1 initial state, 6 BoatSpots to hit
    shortTrace: {
        all b : Board | wellformed[b]
        traces
    } for 6 Board is unsat

    // can't be an initial board and a final board
    initAndFinal: {
        some b : Board | init[b] and final[b]
    } is unsat

    // can move anywhere from an initial board. as long as the next board is not also an initial board
    moveFromInit: {
        all pre, post : Board | (wellformed[pre] and wellformed[post] and init[pre] and not init[post]) implies {
            all r, c : Int | {
                move[pre, post, r, c]
            } 
        }
    } is theorem

    // // can't move anywhere from a final board
    cantMoveFromFinal : {
        all pre, post : Board | wellformed[pre] and final[pre] implies {
            no r, c : Int | {
                move[pre, post, r, c]
            }
        }
    } is theorem

}
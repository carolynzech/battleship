#lang forge/bsl "curiosity modeling tests" "le4s1dpsmgywfv79@gmail.com"

open "single_player.frg"

// Tests for each predicate

test suite for wellformed {}

test suite for init {}

test suite for final {}

test suite for validLocation {}

test suite for move {}

test suite for doNothing {}

test suite for traces {}

// should have some sat/unsat tests, and maybe theorem tests too, for the predicates working together
#lang forge

sig node {
    num: one Int
}

sig State{
    n: one node
}

run {} for exactly 1 node, exactly 3 State
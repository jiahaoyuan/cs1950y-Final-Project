#lang forge

---------------- Part 1. Sig Declaration ----------
sig Status {}
sig Follower extends Status{}
sig Candidate extends Status{}
sig Leader extends Status{}

sig Node {
    id: one Int
}

sig Majority {
    constant: one Int
}

sig State {
    network: set Node,
    step: one Int,
    leaders: set Node,
    followers: set Node,
    candidates: set Node,
    voteTo: set Node->Node,
    trm: set Node->Int -- e.g. for node n, its term is term[n] or n.term
}


-----------------------------Helper Predicates------------------------------------
pred stateInvariant[nodeCount: Int] {
    all s: State | #s.network = nodeCount and
                   s.network = s.leaders + s.followers + s.candidates      
}

fun dom [r: univ->univ] : set (r.univ) { r.univ }

------------------------------State-------------------------------

state[State] initState {
    all n: network | n->sing[0] in trm
    #trm = 3
    no voteTo
    step = sing[0] 
    no leaders
    no candidates
    followers = network
    Majority.constant = sing[3] -- if #network = 5
}

------------------------------Transition--------------------------

 transition[State] timeout { 
    one n : network - leaders | let next_trm = sing[add[sum[trm[n]], 1]] |{
        -- term ++
        trm' = trm - n->trm[n]
        trm' = trm + n->next_trm
        n in followers implies {
            candidates' = candidates + n
            followers' = followers - n
        } else {
            followers' = followers
            candidates' = candidates
        }
    }
    network' = network
    step' = sing[add[sum[step], 1]]
    leaders' = leaders
    voteTo' = voteTo
}

/**
transition[State] timeout {
    network' = network
    step' = sing[add[sum[step], 1]]
    leaders' = leaders
    followers' = followers
    candidates' = candidates
    voteTo' = voteTo
    trm' = trm
}*/

transition[State] advance {
    timeout[this, this']
}
------------------------------Run----------------------

trace<|State, initState, advance, _|> election {}

pred wellFormed {
    stateInvariant[3]
    Status = Follower + Candidate + Leader
    all n: Node | all s: State | n in s.network
    #trm = 3
    all n: Node | #voteTo[n] < 2 
}

run <|election|> {wellFormed} for exactly 3 Node, 3 State
                                          









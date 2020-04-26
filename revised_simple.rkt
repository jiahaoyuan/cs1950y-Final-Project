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
    no voteTo
    step = sing[0] 
    no leaders
    no candidates
    followers = network
    Majority.constant = sing[2] -- if #network = 3
}

------------------------------Transition--------------------------

-- randomly select a follower or a leader to timeout
transition[State] timeout { 
    one n : network - leaders | let cur_trm = trm[n] |
        let next_trm = sing[add[sum[cur_trm], 1]] | {
            -- term ++
            trm' = trm - n->cur_trm + n->next_trm
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

-- randomly select a follower and a candidate
-- the follower should decide if it wanna to vote
-- candidate could also fall back if its term is smaller
transition[State] fol_comm_cand{
    one fol: followers | one cand: candidates { 
        sum[trm[cand]] < sum[trm[fol]]  implies {
            -- update candidate's term to follower's term
            trm' = trm - cand->trm[cand] + cand->trm[fol]
            -- fallback
            candidates' = candidates - cand
            followers' = followers + cand
            -- rest stay the same
            voteTo' = voteTo
        } else {
            sum[trm[cand]] > sum[trm[fol]] and no voteTo[fol] implies {
                voteTo' = voteTo + fol->cand
                trm' = trm - fol->trm[fol] + fol->trm[cand]
                -- rest stay the same
                followers' = followers
                candidates' = candidates
            } else { -- in other situations, do nothing
                    followers' = followers
                    candidates' = candidates
                    voteTo' = voteTo
                    trm' = trm
                }
        }
        network' = network
        step' = sing[add[sum[step], 1]]
        leaders' = leaders
        -- if trm[cand] == trm[fol], do nothing
    }   
}

/**
transition[State] stay_same {
    network' = network
    step' = sing[add[sum[step], 1]]
    leaders' = leaders
    followers' = followers
    candidates' = candidates
    voteTo' = voteTo
    trm' = trm
}*/

transition[State] advance {
    #candidates > 0 and #followers = 0 implies {
        timeout[this, this']
    }
    #candidates = 0 and #followers > 0 implies {
        timeout[this, this']
    }
    #candidates > 0 and #followers > 0 implies {
        fol_comm_cand[this, this']
        timeout[this, this']
    }
}
------------------------------Run----------------------

trace<|State, initState, advance, _|> election {}

inst bounds {
    #Node = 5
    #State = 3
}

pred wellFormed {
    stateInvariant[3]
    Status = Follower + Candidate + Leader
    all n: Node | all s: State | {
        n in s.network
        #n.(s.trm) = 1
        #n.(s.voteTo) < 2 
    }
}

run <|election|> {wellFormed} for bounds
                                          









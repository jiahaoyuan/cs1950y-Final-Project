#lang forge

---------------- Part 1. Sig Declaration ----------
sig Status {}
sig Follower extends Status{}
sig Candidate extends Status{}
sig Leader extends Status{}

sig Node {
    --id: one Int
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
    some fol: followers | some cand: candidates {
    -- ***********************************************
    -- Jiahao's comment: WARNING! If you say one fol or one cand, it is unsat!
    -- one means one and only one satisfy the following.
    -- Use some! It will pick any individuals or a combination of individuals.
    --fol = Node1 or Node2 run 1
    -- ***********************************************
        sum[trm[cand]] < sum[trm[fol]]  implies {
            -- update candidate's term to follower's term
            trm' = trm - cand->trm[cand] + cand->trm[fol]
            -- fallback
            candidates' = candidates - cand
            followers' = followers + cand
            -- rest stay the same
            voteTo' = voteTo
        } else {
            sum[trm[cand]] > sum[trm[fol]] and no voteTo[fol] implies { -- now testcase here
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
        
    }
    network' = network
    step' = sing[add[sum[step], 1]]
    leaders' = leaders
}

-- Randomly choosing a candidate and a leader
-- either the leader will vote for the candidate and fall back
-- or the candidate will fall back to follower
-- transition[State] cand_comm_leader {
    -- TODO: jiayang
-- }


-- Randomly choosing two candidate
-- one may vote for the other
-- transition[State] cand_comm_cand {
    -- TODO: jiayang
-- }



-- transition[State] become_leader {
    -- TODO: jiahao
--}


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
    /**
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
    */
    fol_comm_cand[this, this']
}
------------------------------Run----------------------
state[State] testState { -- 1 cand, t=0, -- rest fol, t=0
    all n: followers | n->sing[0] in trm
    #candidates = 1
    one n: candidates | n->sing[0] in trm
    followers = network - candidates
    no leaders
    no voteTo
    step = sing[0] 
    Majority.constant = sing[2] -- if #network = 3
}



--trace<|State, initState, advance, _|> election {}
trace<|State, testState, advance, _|> election {}

inst bounds {
    #Node = 3
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
                                          









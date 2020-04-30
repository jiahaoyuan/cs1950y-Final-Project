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
                   s.network = s.leaders + s.followers + s.candidates and
                   no s.leaders & s.followers and
                   no s.leaders & s.candidates and
                   no s.followers & s.candidates -- no status can have more than two status
}

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
    -- ************************************************
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
            sum[trm[cand]] > sum[trm[fol]] or (sum[trm[cand] = sum[trm[fol] and no voteTo[fol]]]) implies { -- now testcase here
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
transition[State] cand_comm_leader {
    some cand: candidates | some lead: leaders {
         -- 1. if there's a leader
            -- 1.1 and the leader's trm is higher, the candidate should fall back to follower
            sum[trm[cand]] <= sum[trm[lead]] implies { 
                candidates' = candidates - cand
                followers' = followers + cand
                leaders' = leaders
                voteTo' = voteTo
                trm' = trm - cand->trm[cand] + cand->trm[lead]
            } 
            
            -- 1.2. and the leader's trm is smaller, the leader should fall back to follower and vote the candidate
            else { 
                candidates' = candidates
                followers' = followers + lead
                leaders' = leaders - lead
                voteTo' = voteTo + lead->cand
                trm' = trm - lead->trm[lead] + lead->trm[cand]
               
            } 
        -- 2. if there's no leader, nothing should happen
        
        network' = network
        step' = sing[add[sum[step], 1]]
    } 
}


-- Randomly choosing two candidate
-- one may vote for the other
transition[State] cand_comm_cand {
    some cand1: candidates |some cand2: candidates - cand1 {
        sum[trm[cand1]] > sum[trm[cand2]] implies {
          -- 1. if cand1 has a higher term, cand2 will fall back to follower and should vote to cand1
          candidates' = candidates - cand2
          followers' = followers + cand2
          voteTo' = voteTo + cand2->cand1
          trm' = trm - cand2->trm[cand2] + cand2->trm[cand1]
        }
        
        sum[trm[cand1]] < sum[trm[cand2]] implies {
          -- 2. if cand2 has a higher term, cand1 will fall back to follower and should vote to cand1
          candidates' = candidates - cand1
          followers' = followers + cand1
          voteTo' = voteTo + cand1->cand2
          trm' = trm - cand1->trm[cand1] + cand1->trm[cand2]
      
        }
        sum[trm[cand1]] = sum[trm[cand2]] implies {
            candidates' = candidates
            followers' = followers
            voteTo' = voteTo
            trm' = trm
        }
    }
    leaders' = leaders
    network' = network
    step' = sing[add[sum[step], 1]]
}



transition[State] become_leader {
    some cand: candidates|
        -- 1. if one candidate gets the majority of votes, it wins and will become the leader
        -- either a candidate wins or no winner
        #(voteTo.cand) >= sum[Majority.constant] implies {
            candidates' =  candidates - cand
            leaders' = leaders + cand
            followers' = network - candidates' - leaders'
            no voteTo'
            trm' = trm -- need to rewrite this to make sure all nodes in the network have the same trm
        } else {     
            candidates' = candidates
            leaders' = leaders 
            followers' = followers
            voteTo' = voteTo
            trm' = trm
        }
    network' = network
    step' = sing[add[sum[step], 1]]        
}

-- To simulate leader sending heatbeat to other members
-- if the leader's term is greater or equal:
-- reset all the attr of this member to wanted
-- otherwise, leader fallback 
transition[State] heartbeat {
    some n : leaders | some m: network-n {--could be more than one leader, each at different term
        sum[trm[n]] >= sum[trm[m]] implies {
            -- reset the member's attribute term, status
            trm' = trm - m->trm[m] + m->trm[n]
            
            m in candidates implies {
                candidates' = candidates - m
                followers' = followers + m
                leaders' = leaders
            }
            
            m in leaders implies {
                leaders' = leaders - m
                followers' = followers + m
                candidates' = candidates
            }
        
            m in followers implies {
                leaders' = leaders
                followers' = followers
                candidates' = candidates
            }
        } else {
            -- leader's term is smaller, reset leader
            trm' = trm - n->trm[n] + n->trm[m]
            leaders' = leaders - n
            followers' = followers + n
            candidates' = candidates
        }
    }
    network' = network
    step' = sing[add[sum[step], 1]]
    voteTo' = voteTo
}

--TODO: add a livig new node into the network
--transition[State] addNode {}

--TODO: one node die, with means it no longer responds to any contact
-- and no timeout and etc. 
--transition[State] die {}

transition[State] advance {
    // TODO
    --heartbeat[this, this']
}
------------------------------Run----------------------
state[State] testState {
    all n: followers | n->sing[0] in trm
    no voteTo
    step = sing[0] 
    no leaders
    #candidates = 1
    one n: candidates | n->sing[0] in trm
    followers = network - candidates
    Majority.constant = sing[2] -- if #network = 3
}


trace<|State, testState, advance, _|> election {}


inst bounds {
    #Node = 3
    #State = 2
}

pred wellFormed {
    stateInvariant[3]
    
    all n: Node | all s: State | {
        n in s.network
        one n.(s.trm)
        lone n.(s.voteTo)
    }
}


run <|election|> {wellFormed} for bounds




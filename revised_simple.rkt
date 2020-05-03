#lang forge

---------------- Part 1. Sig Declaration ----------
sig Node {
    --id: one Int
}

sig Majority {
    constant: one Int
}

sig State {
    network: set Node, -- nodes in the network
    reserve: set Node, -- nodes not in the network
    step: one Int,
    leaders: set Node,
    followers: set Node,
    candidates: set Node,
    voteTo: set Node->Node,
    trm: set Node->Int  -- e.g. for node n, its term is term[n] or n.term
}

-- Events
sig Event {
    pre: one State,
    post: one State
}

sig Timeout extends Event {}
sig Foll_Cand extends Event {}
sig Cand_Leader extends Event {}
sig Cand_Cand extends Event {}
sig CountVotes extends Event {}
sig Heartbeat extends Event {}
sig AddNode extends Event {}
sig FailNode extends Event {}



-----------------------------Helper Predicates------------------------------------
pred stateInvariant[nodeCount: Int] {
    all s: State | Node = s.network + s.reserve and -- Nodes must either be in network or reserve
                   no s.network & s.reserve and
                   
                   s.network = s.leaders + s.followers + s.candidates and -- Nodes must be a follower or a leader or a candidate
                   no s.leaders & s.followers and
                   no s.leaders & s.candidates and
                   no s.followers & s.candidates and
                   
                   #Majority = 1 and -- Majority.constant is the number of the majority in network
                   Majority.constant = sing[2] -- if #network = 3
                   
   
}

--------------------------------Transitions---------------------------------------
-- Transition 1: timeout
-- randomly select a follower or a candidate to timeout, when a node timeouts, it should become
-- a candidate and increment its term by 1. Each candidate will vote to itself.
transition[State] timeout {
    -- no need to timeout for candidates or leaders  
    some n : followers + candidates| let cur_trm = trm[n] | 
        let next_trm = sing[add[sum[cur_trm], 1]]  {
            trm' = trm - n->cur_trm + n->next_trm -- increment n's term
            candidates' = candidates + n          -- n becomes a candidate from a follower
            followers' = followers - n
            voteTo' = voteTo + n->n               -- vote for itself
        }
        
        network' = network
        reserve' = reserve
        step' = sing[add[sum[step], 1]]           
        leaders' = leaders
    }

-- Transition 2: followers communicate candidates
-- randomly select a follower and a candidate
-- the follower should decide if it wanna vote
-- candidate could also fall back if its term is smaller than the follower's term
transition[State] fol_comm_cand{
    some fol: followers | some cand: candidates {
        sum[trm[cand]] < sum[trm[fol]]  implies {
            trm' = trm - cand->trm[cand] + cand->trm[fol] -- update candidate's term to follower's term
            candidates' = candidates - cand               -- fallback
            followers' = followers + cand
            voteTo' = voteTo - cand->cand
        } else {
            ((sum[trm[cand]] > sum[trm[fol]]) or (sum[trm[cand]] == sum[trm[fol]] and no voteTo[fol])) implies{ 
                some voteTo[fol] implies { -- if this fol has voted before, delete the old vote record and vote again
                    voteTo' = voteTo + fol->cand - fol->fol.voteTo
                }
                else { 
                     voteTo' = voteTo + fol->cand
                }
                
                trm' = trm - fol->trm[fol] + fol->trm[cand] -- update the follower's term to the candidate's term
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
    
    reserve' = reserve
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
                voteTo' = voteTo - cand->cand
                trm' = trm - cand->trm[cand] + cand->trm[lead]
            } 
            
            -- 1.2. and the leader's trm is smaller, the leader should fall back to follower and vote the candidate
            else { 
                candidates' = candidates
                followers' = followers + lead
                leaders' = leaders - lead
                voteTo' = voteTo + lead->cand - lead->lead
                trm' = trm - lead->trm[lead] + lead->trm[cand]
               
            } 
        -- 2. if there's no leader, nothing should happen
        reserve' = reserve
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
          voteTo' = voteTo + cand2->cand1 - cand2->cand2
          trm' = trm - cand2->trm[cand2] + cand2->trm[cand1]
        }
        
        sum[trm[cand1]] < sum[trm[cand2]] implies {
          -- 2. if cand2 has a higher term, cand1 will fall back to follower and should vote to cand1
          candidates' = candidates - cand1
          followers' = followers + cand1
          voteTo' = voteTo + cand1->cand2 - cand1->cand1
          trm' = trm - cand1->trm[cand1] + cand1->trm[cand2]
      
        }
        sum[trm[cand1]] = sum[trm[cand2]] implies {
            candidates' = candidates
            followers' = followers
            voteTo' = voteTo
            trm' = trm
        }
    }
    reserve' = reserve
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
            voteTo' = voteTo
            trm' = trm -- need to rewrite this to make sure all nodes in the network have the same trm
        } else {     
            candidates' = candidates
            leaders' = leaders 
            followers' = followers
            voteTo' = voteTo
            trm' = trm
        }
    reserve' = reserve
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
            let newTerm = trm - m->trm[m] + m->trm[n] | {
            trm' = newTerm
            
            m in candidates implies {
                candidates' = candidates - m
                followers' = followers + m
                leaders' = leaders
                voteTo' = voteTo - m->m
            }
            
            m in leaders implies {
                leaders' = leaders - m
                followers' = followers + m
                candidates' = candidates
                voteTo' = voteTo - m->m
            }
        
            m in followers implies {
                leaders' = leaders
                followers' = followers
                candidates' = candidates
                trm[m] = trm[n] implies (voteTo' = voteTo) else (voteTo' = voteTo - m->m)
            }
        }
            
        } else {
            -- leader's term is smaller, reset leader
            trm' = trm - n->trm[n] + n->trm[m]
            leaders' = leaders - n
            followers' = followers + n
            candidates' = candidates
            voteTo' = voteTo - n->n
        }
    }
    reserve' = reserve
    network' = network
    step' = sing[add[sum[step], 1]]
}

--TODO: add a livig new node into the network
transition[State] addNode {
    one n: reserve  {
        network' = network + n
        reserve' = reserve - n
        followers' = followers + n
        candidates' = candidates
        leaders' = leaders
        trm' = trm + n->sing[0]
        voteTo' = voteTo
        step' = sing[add[sum[step], 1]]
    }
}


--TODO: one node die, which means it no longer responds to any contact
-- and no timeout and etc. 
transition[State] die {
    some n: network {
        network' = network - n
        reserve' = reserve + n
        trm' = trm - n->trm.n
        voteTo' = voteTo
        step' = sing[add[sum[step], 1]]
        
        n in followers implies {
          followers' = followers - n
          candidates' = candidates
          leaders' = leaders
        }
        
        n in candidates implies {
          followers' = followers 
          candidates' = candidates - n
          leaders' = leaders
        }
        
        n in leaders implies {
          followers' = followers
          candidates' = candidates
          leaders' = leaders - n
        }
   }
      
}

----------------------Healthy Network -------------------
transition[State] healthStateTransition[e: Event] {
    e.pre = this
    e.post = this'
    e in Timeout implies timeout[this, this']
    e in Cand_Cand implies cand_comm_cand[this, this']
    e in Foll_Cand implies fol_comm_cand[this, this']
    e in Cand_Leader implies cand_comm_leader[this, this']
    e in CountVotes implies become_leader[this, this']
    e in Heartbeat implies heartbeat[this, this']
}

transition[State] healthElectionTransition {
    #leaders > 0 implies {
        # candidates <= 0 implies {
            one e: Timeout+Heartbeat | stateTransition[this, this', e]
        }else {
            one e: Event | stateTransition[this, this', e]
        }
    } else {
        #candidates > 0 implies {
            one e: Event-Heartbeat | stateTransition[this, this', e]
        } else {
            -- no leaders or candidates:
            one e: Timeout | stateTransition[this, this', e]
        }
    }   
}

----------------------Unhealthy Network ----------------------
transition[State] unhealthStateTransition[e: Event] {}

transition[State] unhealthElectionTransition {}
------------------------------Run----------------------
/**
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

state[State] testState2 {
    all n: network | n->sing[0] in trm 
    no voteTo
    step = sing[0] 
    followers = network - candidates - leaders
    Majority.constant = sing[2] -- if #network = 3
}
*/

----------------------------------------------------------------
state[State] threeFollowers {
    all n: network | n->sing[0] in trm
    no voteTo
    step = sing[0]
    no leaders
    no candidates
    followers = network 
}

trace<|State, threeFollowers, electionTransition, _|> election {}

pred wellFormedEvent {
    Event = Timeout + Foll_Cand+Cand_Leader+Cand_Cand+CountVotes+Heartbeat
    all s: election.tran.State | one e: Event | e.pre = s
}
----------------------------Bounds-------------------------------
inst bounds {
    #Node = 3
    #State = 10
    #Event = 9
}

pred wellFormed {
    wellFormedEvent
    stateInvariant[3]
    all n: Node | all s: State | {
        n in s.network implies {
            one n.(s.trm)
            lone n.(s.voteTo)
        }
    }
}
----------------------------Testing----------------------------------

-- Finds a leader within the bounds 
pred atLeastOneLeader {
    wellFormed
    some s: State | #s.leaders >= 1
}
-- Finds two leaders of different term
-- TODO: DEBUG
pred twoLeadersDiffTerm {
    wellFormed
    some s: State | {
        #s.leaders = 2 
        some n1: s.leaders | some n2: s.leaders-n1 {
            s.trm[n1] != s.trm[n2]
        }
    }  
}
-- Finds two leaders of the same term
pred twoLeadersSameTerm {
    wellFormed
    some s: State | {
        #s.leaders = 2 
        some n1: s.leaders | some n2: s.leaders-n1 {
            s.trm[n1] = s.trm[n2]
        }
    }  
}

check <|election|> {
   --not atLeastOneLeader
    not twoLeadersDiffTerm
   -- not twoLeadersSameTerm
} for bounds

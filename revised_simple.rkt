#lang forge

---------------- Section 1. Sig Declaration ----------
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



----------------------Section 2. Helper Predicates------------------------------------
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


----------------------Section 3. Transitions---------------------------------------
-- Transition 1: timeout
-- randomly select a follower or a candidate to timeout, when a node timeouts, it should become
-- a candidate and increment its term by 1. Each candidate will vote to itself.
transition[State] timeout {
    -- no need to timeout for candidates or leaders  
    some n : followers + candidates| let cur_trm = trm[n] | 
        let next_trm = sing[add[sum[cur_trm], 1]]  {
            trm' = trm - n->cur_trm + n->next_trm -- increment n's term
            n in followers implies {
                candidates' = candidates + n      -- n becomes a candidate from a follower
                followers' = followers - n
                voteTo' = voteTo + n->n           -- vote for itself                
            }
            n in candidates implies {             -- only update the term
                candidates' = candidates
                followers' = followers
                voteTo' = voteTo - voteTo.n->n + n->n
            }
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
       -- 1. if the candidate's term is smaller, it should fall back
        sum[trm[cand]] < sum[trm[fol]]  implies {
            trm' = trm - cand->trm[cand] + cand->trm[fol] -- update candidate's term to follower's term
            candidates' = candidates - cand               -- fallback
            followers' = followers + cand
            voteTo' = voteTo - cand->cand
        } else {
            -- 2.1 if the candidate's term is larger or (the candidates's term equals the follower's term and the follower
            --    has NOT voted), now the follower should vote to the candidate
            ((sum[trm[cand]] > sum[trm[fol]]) or (sum[trm[cand]] = sum[trm[fol]] and no voteTo[fol])) implies{ 
                some voteTo[fol] implies { -- if this fol has voted before, delete the old vote record and vote again
                    voteTo' = voteTo + fol->cand - fol->fol.voteTo
                }
                else { 
                     voteTo' = voteTo + fol->cand
                }
                
                trm' = trm - fol->trm[fol] + fol->trm[cand] -- update the follower's term to the candidate's term
                followers' = followers
                candidates' = candidates
            } else {
            -- 2.2 in other situations, do nothing
                    followers' = followers
                    candidates' = candidates
                    voteTo' = voteTo
                    trm' = trm
            }
        }  
    }   
    reserve' = reserve
    network' = network
    step' = sing[add[sum[step], 1]] -- update the step
    leaders' = leaders
}

-- Transition 3: candidates communicate leaders
-- Randomly choosing a candidate and a leader
-- either the leader will fall back and then vote for the candidate 
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
                voteTo' = voteTo + lead->cand -- TODO: is it possible that leader voted before?
                trm' = trm - lead->trm[lead] + lead->trm[cand]
               
            }         
        reserve' = reserve
        network' = network
        step' = sing[add[sum[step], 1]]
    }
    -- 2. if there's no leader, nothing should happen
}

-- Transition 4: candidates communicate candidates
-- Randomly choosing two candidate
-- one may vote for the other
transition[State] cand_comm_cand {
    some cand1: candidates | some cand2: candidates - cand1 {
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
          -- 3. if terms are equal, nothing should happen
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

-- Transition 5: one candidate become a leader
-- if a candidate receives the majority of votes in the network, it will then become a leader
transition[State] become_leader {
    some cand: candidates|
        -- 1. if one candidate gets the majority of votes, it wins and will become the leader
        -- either a candidate wins or no winner
        #(voteTo.cand) >= sum[Majority.constant] implies {
            candidates' =  candidates - cand
            leaders' = leaders + cand
            followers' = network - candidates' - leaders'
            voteTo' = voteTo
            trm' = trm 
        } else {
        -- 2. if this candidate is not qualified to win, nothing should happen
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

-- Transition 6: the leader sends heartbeat
-- To simulate leader sending heatbeat to other members
-- if the leader's term is greater or equal, then reset all the attr of this member to wanted
-- otherwise, leader fallback 
transition[State] heartbeat {
    some n : leaders | some m: network - n {--could be more than one leader, each at different term
        -- 1. if n's term is higher, reset m's term and type
        sum[trm[n]] >= sum[trm[m]] implies {
            let newTerm = trm - m->trm[m] + m->trm[n] | {
                trm' = newTerm
                sum[trm[n]] > sum[trm[m]] implies { -- if m voted before, delete the old vote record
                    voteTo' = voteTo - m->(m.voteTo)
                }
                else{
                    voteTo' = voteTo
                }
                    
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
           }
        } else {
            -- 2. if the leader's term is smaller, reset leader
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

-- Transition 7: add one node into the network from reserve
transition[State] addNode {
    one n: reserve  {
        network' = network + n
        reserve' = reserve - n
        
        followers' = followers + n
        candidates' = candidates
        leaders' = leaders
        
        trm' = trm + n->sing[0] --TODO: if making it start at trm zero, then we should remove its voteTo in die
        voteTo' = voteTo
        step' = sing[add[sum[step], 1]]
    }
}

-- Transition 8: let one node die and it can no longer responds to others
transition[State] die {
    some n: network {
        network' = network - n
        reserve' = reserve + n
        trm' = trm - n->(n.trm)
        some voteTo[n] implies voteTo' = voteTo - n->voteTo[n] else voteTo' = voteTo -- mod
        --voteTo' = voteTo
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

-------------------Section 4. Healthy Network -------------------
transition[State] healthyStateTransition[e: Event] {
    e.pre = this
    e.post = this'
    e in Timeout implies timeout[this, this']
    e in Cand_Cand implies cand_comm_cand[this, this']
    e in Foll_Cand implies fol_comm_cand[this, this']
    e in Cand_Leader implies cand_comm_leader[this, this']
    e in CountVotes implies become_leader[this, this']
    e in Heartbeat implies heartbeat[this, this']
}

transition[State] healthyElectionTransition {
    #leaders > 0 implies {
        # candidates <= 0 implies {
            one e: Timeout+Heartbeat | healthyStateTransition[this, this', e]
        }else {
            one e: Event | healthyStateTransition[this, this', e]
        }
    } else {
        #candidates > 0 implies {
            one e: Event-Heartbeat | healthyStateTransition[this, this', e]
        } else {
            -- no leaders or candidates:
            one e: Timeout | healthyStateTransition[this, this', e]
        }
    }   
}

----------------------Section 5. Unhealthy Network ----------------------
transition[State] unhealthyStateTransition[e: Event] {
    e.pre = this
    e.post = this'
    e in Timeout implies timeout[this, this']
    e in Cand_Cand implies cand_comm_cand[this, this']
    e in Foll_Cand implies fol_comm_cand[this, this']
    e in Cand_Leader implies cand_comm_leader[this, this']
    e in CountVotes implies become_leader[this, this']
    e in Heartbeat implies heartbeat[this, this']
    --e in AddNode impilie
    e in AddNode implies addNode[this, this']
    e in FailNode implies die[this, this']
}

transition[State] unhealthyElectionTransition {
    #leaders > 0 implies {
        # candidates <= 0 implies {
            one e: Timeout+Heartbeat+AddNode+FailNode | healthyStateTransition[this, this', e]
        }else {
            one e: Event | healthyStateTransition[this, this', e]
        }
    } else {
        #candidates > 0 implies {
            one e: Event-Heartbeat | healthyStateTransition[this, this', e]
        } else {
            -- no leaders or candidates:
            one e: Timeout+AddNode+FailNode | healthyStateTransition[this, this', e]
        }
    }   
}

------------------------- Section 6. Initial State ----------------------

state[State] threeFollowers {
    all n: network | n->sing[0] in trm
    no voteTo
    step = sing[0]
    no leaders
    no candidates
    followers = network 
}

trace<|State, threeFollowers, healthyElectionTransition, _|> election {}

trace<|State, threeFollowers, unhealthyElectionTransition, _|> unhealthyElection {}

pred wellFormedEventHealthy {
    Event = Timeout + Foll_Cand + Cand_Leader + Cand_Cand + CountVotes + Heartbeat
    all s: election.tran.State | one e: Event | e.pre = s
}

pred wellFormedEventUnhealthy {
    Event = Timeout + Foll_Cand + Cand_Leader + Cand_Cand + CountVotes + Heartbeat -- TODO: need to add die and addition
    all s: election.tran.State | one e: Event | e.pre = s
}

pred wellFormed {
    -- wellFormedEvent -- wellFormedEventHealthy and wellFormedEventUnhealthy will be added seperated into run
    stateInvariant[3]
    all n: Node | all s: State | {
        n in s.network implies {
            one n.(s.trm)
            lone n.(s.voteTo)
        }
    }
}

inst bounds {
    #Node = 3
    #State = 10
    #Event = 9
}
----------------------------Section 7. Correctness Testing, Healthy Network----------------------------------

-- Finds a leader within the bounds 
pred atLeastOneLeader {
    wellFormed
    wellFormedEventHealthy
    some s: State | #s.leaders >= 1
}
-- Finds two leaders of different term
-- TODO: DEBUG
pred twoLeadersDiffTerm {
    wellFormed
    wellFormedEventHealthy
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
    wellFormedEventHealthy
    some s: State | {
        #s.leaders = 2 
        some n1: s.leaders | some n2: s.leaders-n1 {
            s.trm[n1] = s.trm[n2]
        }
    }  
}

--run <|election|> {
   --atLeastOneLeader  --sat
   --twoLeadersDiffTerm --sat
   --twoLeadersSameTerm -- unsat
--} for bounds

----------------------------Section 8. Correctness Testing, Unhealthy Network----------------------------------
-- Finds a leader within the bounds 
pred atLeastOneLeaderUnHealthy {
    wellFormed
    wellFormedEventHealthy
    some s: State | #s.leaders >= 1
}

run <|unhealthyElection|> {
   atLeastOneLeader  --sat
   --twoLeadersDiffTerm --sat
   --twoLeadersSameTerm -- unsat
} for bounds


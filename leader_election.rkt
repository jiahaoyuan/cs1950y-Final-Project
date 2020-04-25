#lang forge

---------------- Part 1. Sig Declaration ----------
sig Status {}
sig follower extends Status{}
sig candidate extends Status{}
sig leader extends Status{}

sig Node{
    term: one Int,
    voteFrom: set Node,
    voteTo: set Node, -- #voteTo should be 0 or 1
    clock: one Int,
}

-- a network contains all the nodes
sig Network{
    member: set Node
}

-- a State should represent this network at certain time
sig State {
    step: one Int,
    network : one Network,
    leader: set Node,
    follower: set Node,
    candidate: set Node
}

-- some rules that this network need to hold at least
pred networkInvariant {
    Status = follower + candidate + leader
    all s: State {
        s.network = n.leader + n.follower + n.candidate
        #s.network = #n.leader + #n.follower + #n.candidate
        #s.leader <= 1
    }
}

----------------- Part 2. Helper Functions ------------
fun all_nodes [net : one Network]: set Node { net.member }

----------------- Part 3. Transitions ------------
-- clock should minus one each time
-- if clock gets zero, it should timeout
transition[State] clock_count_down {
    -- TODO:
    /**
    *	if clock > 0, clock --;
    *	if clock = 0, timeout, state = candidate, clock = 100, term ++;
    */
    -- does it include follower, candidate, and leader? leader does not timeout
    all n : follower + candidate | {
        n.clock > 1 implies {
            n.clock' = subtract[n.clock, 1]
            n.term' = n.term
            n.voteFrom' = n.voteFrom
            n.voteTo' = n.voteTo     
        }
        n.clock == 1 implies {
            -- reset clock
            n.clock' > 0
            n.clock' < 10
            n.term' = add[n.term, 1]
            -- follower timeout
            n in follower implies {
                n.voteTo' = n.voteTo + n
                v.voteFrom' = n.voteFrom + n
                follower' = follower - n
                candidate' = candidate + n
            }
            -- candidate timeout
            n in candidate implies {} --do nothing
        }
    }
    -- rest stay the same
    step' = add[this.step, 1]
    leader' = this.leader
}

-- selecting one candidate, and one follower to vote
-- currently the candidate does not fall back. It could be in real world though
transition[State] follower_vote_for_cand {
    -- TODO:
    /**
    *if len(candidate) > 0:
    		one n: Nodes:
			cands = findAllCandidates
			m = closest[cands]
			if (m.Term > n.Term) or (n.voteTo = null && m.Term = n.Term):
				n.voteTo = m
				m.voteFrom.append(n)
				n.Term = m.Term
				n.Clock reset
				n.State = Follower
    */
        #this.candidate > 0 implies {
            one c: cands | one n: follower { -- do we fix the other nodes?
                c.Term < n.Term implies{ -- candidate fall back
                    c.Term' = n.Term
                    c.voteTo' = {}
                    c.voteFrom' = {}
                    c.clock' > 1
                    c.clock' < 10
                    -- n stays the same
                    n.term' = n.term
                    n.voteTo' = n.voteTo
                    n.clock' = n.clock
                } else { -- candidate not fallback
                    c.Term > n.Term or (#n.voteTo = 0 and n.Term = c.Term) implies { -- None in Forge?
                        n.voteTo' = n.voteTo + c
                        c.voteFrom' = c.voteFrom + n
                        n.clock' > 1
                        n.clock' < 10
                    }   
                    #n.voteTo > 0 and n.Term = c.Term implies {
                        -- all other attributes of n stay the same
                        n.voteTo' = n.vote
                        n.clock' = n.clock
                        c.voteFrom' = c.voteFrom
                    }
                    -- c's other attributes should hold
                    c.voteTo' = c.voteTo
                    c.clock' = c.clock
                    c.term' = c.term
                }
            }
            -- attributes of n that is not changed no matter what
            n.voteFrom' = n.voteFrom
            n.term' = n.term
            -- network stay the same
            network' = network -- syntax correct?
            -- state's other attribute stay the same
            step' = add[this.step, 1]
            leader' = this.leader
            candidate' = this.candidate
        }
        -- if no candidate, next state stays the same
        #this.candidate = 0 implies this' = this   
    }
}

-- one cand determine if vote for another cand
transition[State] cand_vote_for_cand {
    -- only proceed when more than one candidate
    /**
    #this.candidate > 1 implies {
        let cands = this.candidate | one c1 : cands | one c2 : cands - c1 {
            c1.term > c2.term implies {
                c1.voteTo' = { c2 }
                c2.voteFrom' = c2.voteTo' + c1
            }
            c2.term < c1.term implies {
                c2.voteTo' = { c1 }
                c1.voteFrom' = c1.voteFrom + c2
            }
            -- for the above two conditions, make sure the rest attribute
            -- stays the same
            c1.term > c2.term or c1.term < c2.term implies{
                -- the candidate will fall back when leader are elected
                c1.term' = c1.term
                c1.clock' = c1.clock
                c2.term' = c2.term
                c2.clock' = c2.clock
                this.ne
            }
            c1.term == c2.term implies this' = this
        }
    }
    #this.candidate < 2 implies {
        this' = this
    }
    */
}

transition[State] leader_vote_for_cand {
}

-- one candidate check to see if it can become a leader
transition[State] become_leader {
    -- TODO:
    /**
     for all candidates or just selecting one candidates:
	if voteFrom > half,
 become leader.
 heartbeat = 30
 his clock never count down again, maybe he sends himself heartbeat as well
 */
 
}

-- the leader's heartbeat should count down, only if
-- there exist a leader
transition[State] heartbeat{
    -- TODO:
    /**
heatbeat --
if heartbeat == 0:
heartbeat = 30
for n in nodes:
	reset clock to random between 50 - 100
*/
}

-- we have to randomly choose one of the four transitions available
transition[State] advance {
    #candidate = 0 and #leader = 0 implies {
        clock_count_down[this, this']
    }
    #candidate = 0 and #leader > 0 implies {
        clock_count_down[this, this'] or
        heartbeat[this, this']
    }
    #candidate = 1 and #leader = 0 implies {
        clock_count_down[this, this'] or
        follower_vote_for_cand[this, this'] 
    }
    #candidate = 1 and #leader = 1 implies {
        clock_count_down[this, this'] or
        follower_vote_for_cand[this, this'] 
    }
    #candidate > 1 and #leader = 0 implies {
        clock_count_down[this, this'] or
        follower_vote_for_cand[this, this'] or
        cand_vote_for_cand[this, this']
    }
    #candidate > 1 and #leader > 0 implies {
        clock_count_down[this, this'] or
        follower_vote_for_cand[this, this'] or
        cand_vote_for_cand[this, this'] or
        leader_vote_for_cand[this, this'] or
        heartbeat[this, this']
    }
}



----------------- Part 4. Tests ------------------------
state[State] noLeaderInit{
    -- TODO
}

state[State] oneLeaderEnd{
    -- TODO
}

trace<|State, noLeaderInit, advance, oneLeaderEnd|> noLeaderToOneLeader {}
run<|noLeaderToOneLeader|> {
    networkInvariant
} for exactly 1 Network, 5 Node
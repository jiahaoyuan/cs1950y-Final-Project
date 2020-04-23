#lang forge

---------------- Part 1. Sig Declaration ----------
sig Status {}
sig Follower extends Status{}
sig Candidate extends Status{}
sig Leader extends Status{}

sig Node{
    trm: one Int,
    voteTo: lone Node
}

-- a State should represent this network at certain time
sig State {
    network: set Node, 
    step: one Int,
    leaders: set Node,
    followers: set Node,
    candidates: set Node
}

-----------------------------Helper Predicates------------------------------------
pred stateInvariant[nodeCount: Int] {
    all s: State | #s.network = nodeCount and
                   s.network = s.leaders + s.followers + s.candidates
}

---------------------------State and Transitions-------------------------------

state[State] initState {
    all n: network | n.trm = sing[0] and (no n.voteTo)
    step = sing[0] 
    no leaders
    no candidates
    followers = network
}

transition[State] timeout {
    some new, old: Node | {
        old in followers and 
        -- new node is a replacement for the old node in the subsequent state
        new not in network and
        new.trm = sing[add[sum[old.trm], 1]] and
        new.voteTo = new 
        --- 
        candidates' = candidates + new and
        followers' = followers - old and 
        network' = network - old + new
    }
    step' = sing[add[sum[step], 1]]
    leaders' = leaders
}

transition[State] election {
    some old: network {
        some new: Node-network | {
            new.trm = old.trm
            old in followers and no old.voteTo implies {
                some c: candidates | new.voteTo = c
                followers' = followers + new - old
                candidates' = candidates
                leaders' = leaders
            }
            old in candidates implies {
                some c: candidates | sum[c.trm] > sum[old.trm] implies {
                    candidates' = candidates - old
                    followers' = followers + new 
                } else {
                    candidates' = candidates - old + new
                    followers' = followers
                }
                leaders' = leaders
            }
            old in leaders implies {
                some c: candidates | sum[c.trm] > sum[old.trm] implies {
                    leaders' = leaders - old
                    followers' = followers + new 
                } else {
                    leaders' = leaders - old + new
                    followers' = followers
                }
                candidates' = candidates
            }
            network' = network - old + new
        }
    }
    step' = sing[add[sum[step], 1]]
}

-- we have to randomly choose one of the four transitions available
transition[State] advance {
    #candidates > 0 implies {
        election[this, this']
    }
    #candidates = 0 and #followers > 0 implies {
        timeout[this, this']
    }
}

trace<|State, initState, advance, _|> traces {}

inst bounds {
    #Node <= 15
    #State = 4
}


pred wellFormed {
    stateInvariant[3]
    Status = Follower + Candidate + Leader
    all n: Node | some s: State | n in s.network
}
run <|traces|> {wellFormed} for bounds



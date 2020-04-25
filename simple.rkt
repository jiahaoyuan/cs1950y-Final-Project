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
            -- Jiahao's Comment: here you are assuming that the candidate's term
            -- is always greater. It is true based on your condition in "advance",
            -- but not true in the real world.
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
            -- jiahao's comment: how is the leader elected? Here it is saying
            -- if candidates' term > leaders' term, then leader fall back.
            -- but how is a new leader selected? I did not see where a candidate
            -- becomes a leader? I don't see how it is possible without a majority count.
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


-- Jiahao's Comment: This is a very good simplification! Well done!
-- But, I think we might also missed a lot of details here.
-- This oversimplifies the real world, which is that election
-- and timout are not mutually exclusive. Even if there is candidates,
-- there would still be other candidates timeout due to network latency
-- or network break down. In fact, a node could keep timeout if
-- it temperarily lose network. That is why we might get different
-- terms in each nodes, and the node with the largest term wins.
-- However, since you appart election and timeout, it means that in every
-- election, all the candidates will have the same term. This is not
-- only unrealistic, but also will result in a long time of tie.
-- Raft should be very fault-tolerant, one of which is network partition.
-- It would be the best if we show that our model can deal with this problem.
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



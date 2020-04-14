#lang forge

---------------- Part 1. Sig Declaration ----------
sig Status {}
sig follower extends Status{}
sig candidate extends Status{}
sig leader extends Status{}

sig Node{
    id: one Int,
    role: one Status,
    edge: set Node->Node,
    term: one Int,
    voteFrom: set Node,
    voteTo: one Node,
    clock: one Int,
    heartBeat: one Int
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
-- Jiahao's question: we should have a function or something
-- to initialize the distances between one node to the other
-- how do we do that ???
pred set_distance[??]{
    -- ?? 
}

-- given a network, return all its nodes
fun find_all_candidates[n: Network] : set Node{
    -- TODO
}

-- find the closest node in n's perspective, excluding itself
fun closest[n: Node, ns: set Node] : Node{
    -- TODO
}

----------------- Part 3. Transitions ------------
-- clock should minus one each time
-- if clock gets zero, it should timeout
transition[State] clock_count_down {
    -- TODO:
}

-- one Node determines if it wants to vote for a candidate
transition[State] vote_request {
    -- TODO:
}

-- one candidate check to see if it can become a leader
transition[State] become_leader {
    -- TODO:
}

-- the leader's heartbeat should count down, only if
-- there exist a leader
transition[State] heartbeat_countdown{
    -- TODO:
}

-- we have to randomly choose one of the four transitions available
transition[State] advance {
    clock_count_down[this, this'] or
    vote_request[this, this'] or
    become_leader[this, this'] or
    heartbeat_countdown[this, this'] 
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
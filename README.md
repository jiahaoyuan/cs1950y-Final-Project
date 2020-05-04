# -cs1950y-Final-Project

Due to the one-page length limit, we could not present all details above, but if you are interested, you can see the four-page full README below.

https://docs.google.com/document/d/1fO7SVXHQPxLc_t69k_uN_hcZV3jY-ptZHypIeM5oHA0/edit?usp=sharing
----------------------------------------------------------------------------------------------------------------------------
Background
Our final project is to model the Leader Election Algorithm in Raft, which is a consensus algorithm commonly used in distributed systems. 
Results
By using Forge, we successfully finished our Foundation Goal in which we used Sigs and Predicates to simulate a network in Raft.
    Also, we implemented 8 transitions to simulate events that might happen in a network and accomplished our Target Goal to prove the Leader Election Algorithm we modeled actually works. Several traces were made to present that one leader will be elected eventually and no more than one leader of the same term will be elected. Plus, we also took network partitions and network delay by simulating that if the nodes are divided into two groups, and no Transition has picked nodes from two partitions at the same time.
    As for the Reach Goal, due to the limit of time and remote collaboration, we only finished part of it, which is to prove that our model is fault tolerant. If something went wrong in our network, by the settings and predicates we made, the network would eventually go back to the normal way.
Sig and Event Declaration
-- Node
-- Majority: which number means majority in the network
-- State (to see the full explanation, go to extended version)		
-- Event: there are 8 events that can happen in the network
Test cases: 
- 1. atLeastOneLeader: sat. To successfully elect a leader in a healthy network.
- 2. twoLeaderDiffTerm: sat. To elect two leaders but with different terms  in a healthy network.
- 3. twoLeaderSameTerm: unsat. To elect two leaders of the same terms in a healthy network.
- 1. atLeastOneLeaderUnHealthy  --sat, In a unhealthy network, elect a leader eventually
- 2. majorityFailsNoLeader -- unsat, If the majority of nodes fail, we could not elect a leader
- 3. oneFailsElectionSucceeds -- sat, If only the minority of nodes fail, we still elect a leader
- 4. twoLeadersSameTermUnhealthy, --unsat, you cannot have two leaders with the same term
     4. Discussion: 
One crucial thing that we would like to prove is that it "eventually" elects a leader. However, it is hard to do so in forge. One approach would be to loose the bounds like this:
"Try to satisfy a trace for N states, with no leader ever elected". If this is unsat, it means that some leaders have to be elected in the process, proving the LTL in the steps of N. Then you can keep cutting N to strict the constraint. Unfortunately, this approach does not work in our model. The reason is that our model uses randomization in transitions, and there exist some traces that do not progress, for example, one node can keep timing out forever. This would be very unlikely to happen in real life, but it is a "possible" scenario. Thus the statement above will be satisfied without giving us guarantees about correctness and safety of the protocol. 

Therefore, although we can show that the algorithm does produce leaders regularly, we could not prove that it always eventually results in at most one leader being elected. 


It’s allowed to have more than one leader but only when they are all in different terms. Since the leader with the higher term will be able to synchronize everyone else once their heartbeats succeed. However, if there are two leaders having the same term in a particular state, this implies inconsistency and shall never happen. Fortunately, our algorithm stands for the challenge. The run "twoLeaderWithSameTerm" cannot be satisfied for both healthy and unhealthy networks. It is one of the most significant achievements of our model. In our midterm project, we have discovered that soundness is more important than completeness. Similarly, electing two leaders is much more of an undesirable issue than no leader getting elected.









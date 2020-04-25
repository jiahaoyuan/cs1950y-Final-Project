
#lang forge
sig Mesh {
    triangles: set Triangle,
    adj: set Triangle -> Triangle
}

sig Triangle {
    edges: set Vertex -> Vertex
}

sig Vertex {}

-------------------------------------------------------------------------------------

fun dom [r: univ->univ] : set (r.univ) { r.univ }

fun dom3 [r: univ->univ->univ] : set((r.univ).univ) { (r.univ).univ }

fun ran [r: univ->univ] : set (univ.r) { univ.r }

fun undirectedEdges [m: Mesh]: Int { subtract[#m.triangles.edges, divide[#m.adj, 2]] }

pred ring [e: Vertex->Vertex] { all v: dom[e] | one v.e and dom[e] in v.^e }

pred symmetric [r: univ -> univ] { ~r in r }

pred irreflexive [r: univ -> univ] { no iden & r }

pred stronglyConnected [r: univ -> univ, s: set univ] {
    all x, y: s | x in y.*r
}

pred meshInvariants {
    -- meshes have at least one triangle
    all m: Mesh | some m.triangles
    -- every triangle appears in a mesh
    all t: Triangle | t in Mesh.triangles
    -- every vertex appears in a triangle
    all v: Vertex | v in dom[Mesh.triangles.edges]
    -- every triangle has 3 edges
    all t: Triangle | #t.edges = 3
    -- the edge set of each triangle forms a ring
    all t: Triangle | ring[t.edges]
    -- no two triangles in the same mesh can share the same edge
    all m: Mesh | all a, b: m.triangles | not a = b => no a.edges & b.edges
    -- triangles in the m.adj relation must be in the set m.triangles
    all m: Mesh | dom[m.adj] + ran[m.adj] in m.triangles
    -- properties of the dual of a mesh, viewing triangles as dual nodes
    all m: Mesh | let r = m.adj, s = m.triangles | symmetric[r] and irreflexive[r] and stronglyConnected[r, s]
    -- triangles that share a pair of incident vertices define the adj relation
    all m: Mesh, a, b: m.triangles | a in m.adj[b] iff one ~(a.edges) & b.edges
    -- Euler's formula: T - 1 = E - V
    all m: Mesh | let T = #m.triangles, E = undirectedEdges[m], V = #dom[m.triangles.edges] |
        subtract[T, 1] = subtract[E, V]
}

-------------------------------------------------------------------------------------

fun nodes [m: one Mesh]: set Node { dom[m.triangles.edges] }

fun elements [m: one Mesh]: set Element { m.triangles }

abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

abstract sig Height {}
one sig Low extends Height {}
one sig Med extends Height {}
one sig High extends Height {}

sig Node extends Vertex {
    H: one Height
}

sig Element extends Triangle {
    slowFlow: one Bool,
    lowNode: one Node
}

sig State {
    step: one Int,
    m: one Mesh,
    W: set Node -> Bool,
    Wt: set Node -> Bool,
    wet: set Element -> Bool
}

pred wetdryInvariants {
    -- booleans can be true or false
    Bool = True + False
    -- water levels can be low, medium, or height
    Height = Low + Med + High
    -- all vertices are nodes
    all v: Vertex | v in Node
    -- all triangles are elements
    all t: Triangle | t in Element
    -- each element, the low node is incident
    all e: Element | e.lowNode in dom[e.edges]
    -- all three of our boolean properties must be exactly true or false
    all s: State {
        let mesh = s.m {
            all n: nodes[mesh] | one s.W[n] and one s.Wt[n]
            all e: elements[mesh] | one s.wet[e]
        }
    }
}

------------------- Helper predicates -----------------------

fun wetNodes [e: Element, s: State]: Int {
    let n = dom[e.edges], w = s.W.True | #(n & w)
}

pred loneDryNode [n: Node, e: Element, s: State] {
    n in dom[e.edges] and n.W[s] = False and wetNodes[e, s] = 2
}

pred make_wet [m: Mesh, n: Node, s: State] {
    some e: elements[m] |
        e.slowFlow = False and loneDryNode[n, e, s]
}

pred active [e: Element, s: State] {
    e.wet[s] = True
    all n: dom[e.edges] | n.Wt[s] = True
}

pred landlocked [m: Mesh, n: Node, s: State] {
    no { e: elements[m] | n in dom[e.edges] and active[e, s] }
}

pred make_dry [m: Mesh, n: Node, s: State] {
    n.Wt[s] = True and landlocked[m, n, s]
}

pred ordering [pre: State, post: State, i: Int] {
    pre.m = post.m
    pre.step = post.step.~succ
    post.step = sing[i]
}

---------------- The steps of the wet/dry algorithm -----------------

state[State] part0 {
    step = sing[0]
    nodes[m].W = nodes[m].Wt
}

transition[State] part1 {
    ordering[this, this', 1]
    elements[m].wet = elements[m].wet'
    /**
     * Fill in part 1
     */
    /**
    * for n in nodes do
    * if Wn and Hn < Hmin, then Wn <- false, Wnt <- false
    */
    all n: nodes[m] | 
        {n.W = True and n.H = Low
        implies {n.W' = False and n.Wt' = False}
        else {n.W' = n.W and n.Wt' = n.Wt}}
}

transition[State] part2 {
    ordering[this, this', 2]
    elements[m].wet = elements[m].wet'
    /**
     * Fill in part 2
     * Note: the make_wet predicate defines the conditions that
     *       cause a node to become (temporarily) wet.
     */
     /**
     * for e in elements do
     * if -Wi for exactly one node i on e and Vss(e) > Vmin
     * then Wti <- true
     */
     all n : nodes[m] | {
          --one n : dom[e.edges] |
              make_wet[m, n, this] 
             
                 --{loneDryNode[n, e, this] and e.slowFlow = False} -- TA: should be State or this?
                 
                 implies {n.Wt' = True}
                 else {n.Wt' = n.Wt}
                 n.W' = n.W
             }
             
     --all e: elements[m] |
     --{ let nodes = dom[e.edges] | one n : nodes |
         --{n.W = False and (nodes-n).W = True and e.slowFlow = False} implies
         --{n.Wt' = True}
     --}
}

transition[State] part3 {
    ordering[this, this', 3]
    all n: nodes[m] | n.W' = n.W and n.Wt' = n.Wt
    /**
     * Fill in part 3
     */
     /**
     * for e in elements do
     *    find nodes i and j of e with highest water surface
     *    elevations ni, nj
     *    if min(Hi, Hj) < 1.2Hmin then
     *       wete <- false
     */
     all e : elements[m] |
          let highNodes = dom[e.edges] - e.lowNode |
              let elevation = highNodes.H |
              {
                  {Low in elevation or Med in elevation}
                  implies {e.wet' = False}
                  else {e.wet' = e.wet}
              }
}

transition[State] part4 {
    ordering[this, this', 4]
    elements[m].wet' = elements[m].wet
    /**
     * Fill in part 4
     * Note: the make_dry predicate defines the conditions that
     *       cause a node to become (temporarily) dry.
     */
     /**
     * for n in nodes do
     * if Wtn and n on only inactive elements then
     * Wtn <- false
     */
     all n : nodes[m] |
         {
             make_dry[m, n, this]
             implies {n.Wt' = False}
             else {n.Wt' = n.Wt}
             n.W' = n.W
         }
}

transition[State] part5 {
    ordering[this, this', 5]
    elements[m].wet' = elements[m].wet
    /**
     * Fill in part 5
     */
     /**
     * for n in nodes do
     * Wn <- Wtn
     */
     all n : nodes[m] |
         n.W' = n.Wt
}

----------- Build some traces and answer some questions --------------

state[State] initAllDry {
    part0[this]
    all n: nodes[m] | n.W = False
}

state[State] initAllWet {
    part0[this]
    all n: nodes[m] | n.W = True
}

state[State] endAllDry {
    all n: nodes[m] | n.W = False
}

state[State] endAllWet {
    all n: nodes[m] | n.W = True
}

transition[State] advance {
    part1[this, this'] or
    part2[this, this'] or
    part3[this, this'] or
    part4[this, this'] or
    part5[this, this']
}

-- Can a mesh start out with all dry nodes and have them all become wet?
trace<|State, initAllDry, advance, endAllWet|> allDryToWet {}
run<|allDryToWet|> {
    meshInvariants
    wetdryInvariants
} for exactly 1 Mesh, exactly 5 State
-- Ans: Unsat

-- Can a mesh start out with all wet nodes and have them all become dry?
trace<|State, initAllWet, advance, endAllDry|> allWetToDry {}
run<|allWetToDry|> {
    meshInvariants
    wetdryInvariants
} for exactly 1 Mesh, exactly 6 State, 1 Triangle
-- Ans: Sat

-- Generate a valid trace
trace<|State, part0, advance, _|> wetdry {}
run<|wetdry|> {
    meshInvariants
    wetdryInvariants
} for exactly 1 Mesh, exactly 6 State

----------------------------------------------------------------------------

state[State] initAnswerQuestion {
    part0[this]
    all n: nodes[m] | n.W = True
    all e: elements[m] | e.slowFlow = True and e.wet = True
    some n: Node | one e: elements[m] | e.lowNode != n
}

transition[State] advanceAnswerQuestion {
    nodes[m].W' = nodes[m].W
    nodes[m].Wt' = nodes[m].Wt
    part1[this, this'] or
    part2[this, this'] or
    part3[this, this'] or
    part4[this, this'] or
    part5[this, this']
}

state[State] dryElementWetNodes {
    one e: elements[m] | e.wet = False and wetNodes[e, this] = 3
}

-- Is it possible for an element with three wet nodes to become dry? 
-- Which step of the algorithm causes an element with three temporarily
-- wet nodes to become dry?
trace<|State, initAnswerQuestion, advanceAnswerQuestion, dryElementWetNodes|> answer {}
run<|answer|> {
    meshInvariants
    wetdryInvariants
} for exactly 1 Mesh, exactly 6 State, exactly 3 Element, exactly 4 Node



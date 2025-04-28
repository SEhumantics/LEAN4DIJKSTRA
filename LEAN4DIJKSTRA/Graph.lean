-- Import required modules.
import Std.Data.HashSet
import Std.Data.HashMap
open Std

namespace GraphDefinitions
/-!!!
This namespace contains data structures to represent a simple directed weighted graph, using adjacency list representation.
!!!-/

--@ Data structures.

-- `Vertex` is a type alias for `String`, representing the vertices of the graph.
abbrev Vertex : Type := String

-- `Weight` is a type alias for `Option Nat`, representing the weights of the edges in the graph.
-- Note that `Weight` can be `none`, which represents positive infinity; or `some n`, which represents a finite weight.
abbrev Weight : Type := Option Nat

-- `POSITIVE_INFINITY` is a constant representing positive infinity for weights.
def POSITIVE_INFINITY : Weight := Option.none

-- Provide an instance of `BEq` for `Weight`, for equality comparison.
instance : BEq (Weight) where
  beq
    -- If both weights are positive infinity, they are equal.
    | Option.none, Option.none => true
    -- If both weights are not positive infinity, compare their values.
    | (some a), (some b) => a == b
    -- Otherwise, they are not equal.
    | _, _ => false

-- Provide an instance of `LT` for `Weight`, for less-than comparison.
instance : LT (Weight) where
  lt
    -- If the first weight is positive infinity, it is not less than the second weight.
    | Option.none, _ => false
    -- If the second weight is positive infinity, the first weight is less than it.
    | (some _), Option.none => true
    -- Otherwise, compare their values.
    | (some a), (some b) => a < b

-- Provide a `Decidable` instance for `Weight` comparisons, for decidable less-than comparison.
instance (a b : Weight) : Decidable (a < b) :=
  match a, b with
  -- If the first weight is positive infinity, it is not less than the second weight.
  | Option.none, _ => isFalse (by simp [LT.lt])
  -- If the first weight is not positive infinity and the second weight is positive infinity, the first weight is less than it.
  | (some _), Option.none => isTrue (by simp [LT.lt])
  -- Otherwise, compare their values.
  | (some a), (some b) => inferInstanceAs (Decidable (a < b))

-- Provide an instance of `HAdd` for `Weight`, for addition of weights.
instance : HAdd (Weight) (Weight) (Weight) where
  hAdd
    -- If the first weight is positive infinity, the result is positive infinity.
    | Option.none, _ => Option.none
    -- If the second weight is positive infinity, the result is positive infinity.
    | _, Option.none => Option.none
    -- Otherwise, add their values.
    | (some a), (some b) => some (a + b)

-- `Edge` is a structure representing an edge in the graph, containing a target vertex and a weight.
structure Edge where
  target : Vertex
  weight : Weight
deriving Repr

-- `Graph` is a type alias for a hash map that maps vertices to a list of edges, representing the adjacency list of the graph.
abbrev Graph : Type := HashMap Vertex (List Edge)

--@ ToString instances for the data structures above.

-- `ToString` instance for `Weight`.
instance : ToString (Weight) where
  toString
    | Option.none => "∞"
    | (some n) => toString n

-- `ToString` instance for `Edge`.
instance : ToString Edge where
  toString (e : Edge) := s!"{e.target} ({e.weight})"

-- `ToString` instance for `Graph`.
instance : ToString Graph where
  toString (g : Graph) :=
    let adjacencyList : List (Vertex × List Edge) := g.toList.mergeSort (
      fun (a : Vertex × List Edge) (b : Vertex × List Edge)
      =>
        a.1 < b.1
    )
    let edges : String := adjacencyList.foldl (
      fun (acc : String) (kv : Vertex × List Edge) =>
        acc ++ s!"{kv.1} -> {kv.2}\n"
      ) ""
    s!"{edges}"

--@ Utility functions.

-- `Graph.empty` creates an empty graph.
def Graph.empty : Graph := HashMap.emptyWithCapacity

-- `Graph.addAdjacencyList` adds an adjacency list to the graph for a given vertex.
def Graph.addAdjacencyList (g : Graph) (v : Vertex) (edges : List Edge) : Graph :=
  g.insert v edges

-- `Graph.getNeighborEdges` retrieves the neighbors edges of a given vertex in the graph.
-- It returns an list of edges connected to the vertex.
-- If the vertex is not found, or if it has no edges to other vertices, it returns an empty list.
def Graph.getNeighborEdges (g : Graph) (v : Vertex) : List Edge :=
  match g.getKey? v with
  | none => []
  | some _ => g[v]!

-- `Graph.isNeighborVertex` checks if a target vertex is a neighbor of a source vertex in the graph.
-- It returns true if the target vertex is a neighbor of the source vertex, and false otherwise.
def Graph.isNeighborVertex (g : Graph) (source : Vertex) (target : Vertex) : Bool :=
  match g.getKey? source with
  | none => false
  | some _ =>
    let edges : List Edge := g[source]!
    edges.any (
      fun (e : Edge) =>
        e.target == target
    )

-- `Graph.listAllVertices` returns a list of all vertices in the graph.
def Graph.listAllVertices (g : Graph) : List Vertex :=
  g.keys


end GraphDefinitions

namespace DijkstraUtils
/-!!!
This namespace contains utility data structures and functions for Dijkstra's algorithm, including the distance map and priority queue.
!!!-/
open GraphDefinitions

--@ Data structure.

-- `Frontier` is a structure representing the frontier of unvisited vertices.
structure FrontierElement where
  -- The vertex in the frontier.
  vertex : Vertex
  -- The distance from the source to this vertex.
  distance : Weight
deriving Repr, BEq

abbrev Frontier : Type := List FrontierElement

-- `DistanceMap` is a structure representing the distance map, containing the distances from the source to each vertex, and arrays of shortest paths.
structure DistanceMap where
  -- The distance map is a hash map that maps vertices to their distances.
  distances : HashMap Vertex Weight
  -- The shortest paths are represented as a hash map that maps a pair of source-target vertices to a list of vertices in the shortest path.
  paths : HashMap (Vertex × Vertex) (List Vertex)

--@ `ToString` instances.

-- `ToString` instance for `FrontierElement`.
instance : ToString FrontierElement where
  toString (fe : FrontierElement) := s!"{fe.vertex} ({fe.distance})"

-- `ToString` instance for `Frontier`.
instance : ToString Frontier where
  toString (f : Frontier) :=
    let elements : String := f.foldl (
      fun (acc : String) (fe : FrontierElement) =>
        acc ++ s!"\n{fe}, "
      ) ""
    s!"{elements}"

-- `ToString` instance for `DistanceMap`.
instance : ToString DistanceMap where
  toString (dm : DistanceMap) :=
    let distancesAsList : List (Vertex × Weight) := dm.distances.toList.mergeSort (
      fun (a : Vertex × Weight) (b : Vertex × Weight)
      =>
        a.1 < b.1
    )
    let distancesElements : String := distancesAsList.foldl (
      fun (acc : String) (kv : Vertex × Weight) =>
        acc ++ s!"\n{kv.1} ({kv.2}), "
      ) ""
    let pathsAsList : List ((Vertex × Vertex) × List Vertex) := dm.paths.toList.mergeSort (
      fun (a : (Vertex × Vertex) × List Vertex) (b : (Vertex × Vertex) × List Vertex)
      =>
        a.1.1 < b.1.1
    )
    let pathsElements : String := pathsAsList.foldl (
      fun (acc : String) (kv : (Vertex × Vertex) × List Vertex) =>
        acc ++ s!"\n{kv.1.1} -> {kv.1.2} : {kv.2}, "
      ) ""
    s!"{distancesElements}\n{pathsElements}"

--@ Utility functions.

-- `DistanceMap.empty` creates an empty distance map.
def DistanceMap.empty : DistanceMap := mk HashMap.emptyWithCapacity HashMap.emptyWithCapacity

-- `Frontier.empty` creates an empty frontier.
def Frontier.empty : Frontier := []

-- `Frontier.push` adds a new element to the frontier, then sorts it by distance.
def Frontier.push (f : Frontier) (fe : FrontierElement) : Frontier :=
  -- Add the new element to the frontier.
  let f' : Frontier := f ++ [fe]

  -- Sort the frontier by distance.
  let f' : Frontier := f'.mergeSort (
    fun (a : FrontierElement) (b : FrontierElement) =>
      a.distance < b.distance
  )

  -- Return the sorted frontier.
  f'

-- `Frontier.peek` retrieves the first element of the frontier.
def Frontier.peek (f : Frontier) : Option FrontierElement :=
  match f with
  | [] => none
  | x :: _ => some x

-- `Frontier.pop` removes the first element from the frontier.
def Frontier.pop (f : Frontier) : Frontier :=
  match f with
  | [] => []
  | _ :: restOfFrontier => restOfFrontier

-- `Frontier.reorganize` reorganizes the frontier by:
-- 1. Updates the distances of the vertices in the frontier if the weights in the distance map are smaller.
-- 2. Sorts the frontier by distance.
def Frontier._reorganizeMapAndReassign (f : Frontier) (dm : DistanceMap) : Frontier :=
  let f' : Frontier := f.map (
    fun (fe : FrontierElement) =>
      match dm.distances[fe.vertex]? with
      | none => fe
      | some d =>
          if d < fe.distance then
            { vertex := fe.vertex, distance := d }
          else
            fe
  )

  -- Return the updated frontier.
  f'

def Frontier.sort (f : Frontier) : Frontier :=
  -- Sort the frontier by distance.
  let f' : Frontier := f.mergeSort (
    fun (a : FrontierElement) (b : FrontierElement) =>
      a.distance < b.distance
  )

  -- Return the sorted frontier.
  f'

def Frontier.reorganize (f : Frontier) (dm : DistanceMap) : Frontier :=
  -- Reorganize the frontier by updating the distances of the vertices in the frontier.
  let f' : Frontier := Frontier._reorganizeMapAndReassign f dm

  -- Sort the frontier by distance.
  let f' : Frontier := Frontier.sort f'

  -- Return the sorted frontier.
  f'

--@ Proofs.

-- Proof that `Frontier.reorganize` won't change the length of the frontier.
theorem Frontier.reorganize_preserves_length (f : Frontier) (dm : DistanceMap) :
  (Frontier.reorganize f dm).length = f.length := by
  unfold Frontier.reorganize
  unfold Frontier._reorganizeMapAndReassign
  unfold Frontier.sort
  simp [List.length_map, List.length_mergeSort]

end DijkstraUtils

namespace DijkstraAlgorithm
/-!!!
This namespace contains the implementation of Dijkstra's algorithm for finding the shortest paths in a graph.
!!!-/
open GraphDefinitions
open DijkstraUtils

--@ Dijkstra's algorithm implementation.

-- `dijkstraAuxiliary` is a recursive auxiliary function that implements the core logic of Dijkstra's algorithm.
def dijkstraAuxiliary (g : Graph) (source : Vertex) (distanceMap : DistanceMap) (frontier : Frontier) : DistanceMap :=
  -- Check if the frontier is empty.
  match frontier with

  -- If the frontier is empty, return the distance map.
  | [] => distanceMap

  -- If the frontier is not empty, proceed with the algorithm.
  | topOfFrontier :: restOfFrontier =>
    -- Get the current vertex from the frontier (surely it has the smallest distance).
    let currentVertex : Vertex := topOfFrontier.vertex

    -- Modify the frontier by removing the current vertex.
    let frontier' : Frontier := restOfFrontier

    -- Get the neighbor edges of the current vertex.
    let neighborEdges : List Edge := Graph.getNeighborEdges g currentVertex

    -- Iterate through the neighbor edges of the current vertex which are still in the frontier.
    let distanceMap' : DistanceMap := neighborEdges.foldl (
      -- For each edge in the neighbor edges...
      fun (acc : DistanceMap) (edge : Edge) =>
        -- Check if the target vertex is in the frontier.
        if frontier'.any (fun (fe : FrontierElement) => fe.vertex == edge.target) then
          -- Calculate the alternative distance.
          let alt : Weight := acc.distances[currentVertex]! + edge.weight
          -- Check if the alternative distance is less than the current distance.
          if alt < acc.distances[edge.target]! then
            -- Update the distance map with the new distance.
            { acc with
              distances := acc.distances.insert edge.target alt,
              paths := acc.paths.insert (source, edge.target) (acc.paths.getD (source, edge.target) [] ++ [currentVertex])
            }
          else
            -- Return the original distance map if no update is needed.
            acc
        else
          -- Return the original distance map if the target vertex is not in the frontier.
          acc
      ) distanceMap

    -- Reorganize the frontier by updating the distances of the vertices in the frontier.
    let frontier' : Frontier := frontier'.reorganize distanceMap'

    -- Recursively call the function with updated parameters.
    dijkstraAuxiliary g source distanceMap' frontier'

-- Proof of termination for `dijkstraAuxiliary`.
-- The function terminates when the frontier is empty.
termination_by frontier.length
-- The recursive call is made with a frontier decreasing in size (`restOfFrontier`), with `reorganize` applied (keeping the same length).
decreasing_by {
  -- Unfold the `reorganize` function.
  unfold Frontier.reorganize
  unfold Frontier._reorganizeMapAndReassign
  unfold Frontier.sort
  -- Use the theorem that proves the length of the frontier is preserved.
  simp [Frontier.reorganize_preserves_length]
}

-- `dijkstra` is the main function that implements Dijkstra's algorithm.
def dijkstra (g : Graph) (source : Vertex) : DistanceMap :=
  -- Initialize the list of vertices in the graph.
  let vertices : List Vertex := Graph.listAllVertices g

  -- Initialize the distance map with positive infinity for all vertices.
  let distanceMap : DistanceMap := vertices.foldl (
    fun (acc : DistanceMap) (v : Vertex) =>
        { acc with distances := acc.distances.insert v POSITIVE_INFINITY }
    ) DistanceMap.empty

  -- Set the distance of the source vertex to 0.
  let distanceMap : DistanceMap := { distanceMap with distances := distanceMap.distances.insert source (some 0) }

  -- Initialize the frontier with the every vertex that isn't the source vertex.
  let frontier : Frontier := vertices.foldl (
    fun (acc : Frontier) (v : Vertex) =>
      if v == source then
        acc
      else
        acc ++ [ { vertex := v, distance := POSITIVE_INFINITY } ]
    ) Frontier.empty

  -- Add the source vertex to the top of the frontier.
  let topOfFrontier : FrontierElement := { vertex := source, distance := some 0 }
  let frontier : Frontier := topOfFrontier :: frontier

  -- Find the resulting distance map using the auxiliary function.
  dijkstraAuxiliary g source distanceMap frontier

end DijkstraAlgorithm

namespace Stuffs

open GraphDefinitions

def generateGraph01 : Graph :=
  -- Create an empty graph.
  let g : Graph := Graph.empty

  -- Reference: https://www.youtube.com/watch?v=71Z-Jpnm3D4
  -- A -> B (5), A -> C (2)
  let g := Graph.addAdjacencyList g "A" [{ target := "B", weight := some 5 }, { target := "C", weight := some 2 }]

  -- B -> C (1), B -> D (4), B -> E (2)
  let g := Graph.addAdjacencyList g "B" [{ target := "C", weight := some 1 }, { target := "D", weight := some 4 }, { target := "E", weight := some 2 }]

  -- C -> E (7)
  let g := Graph.addAdjacencyList g "C" [{ target := "E", weight := some 7 }]

  -- D -> E (6), D -> F (3)
  let g := Graph.addAdjacencyList g "D" [{ target := "E", weight := some 6 }, { target := "F", weight := some 3 }]

  -- E -> F (1)
  let g := Graph.addAdjacencyList g "E" [{ target := "F", weight := some 1 }]

  -- F
  let g := Graph.addAdjacencyList g "F" []

  -- My additional vertices and edges.
  -- H -> I (1)
  let g := Graph.addAdjacencyList g "H" [{ target := "I", weight := some 1 }]
  -- I -> A (1)
  let g := Graph.addAdjacencyList g "I" [{ target := "A", weight := some 1 }]

  -- Return the graph.
  g

def generateGraph02 : Graph :=
  -- Create an empty graph.
  let g : Graph := Graph.empty

  -- A -> B (1), A -> C (5)
  let g := Graph.addAdjacencyList g "A" [{ target := "B", weight := some 1 }, { target := "C", weight := some 5 }]

  -- B -> C (3)
  let g := Graph.addAdjacencyList g "B" [{ target := "C", weight := some 3 }]

  -- C
  let g := Graph.addAdjacencyList g "C" []

  -- D
  let g := Graph.addAdjacencyList g "D" []

  -- Return the graph.
  g

def generateGraph03 : Graph :=
  -- Create an empty graph.
  let g : Graph := Graph.empty

  -- A -> C (2), A -> D (1)
  let g := Graph.addAdjacencyList g "A" [{ target := "C", weight := some 2 }, { target := "D", weight := some 1 }]

  -- B -> C (1), B -> D (4)
  let g := Graph.addAdjacencyList g "B" [{ target := "C", weight := some 1 }, { target := "D", weight := some 4 }]

  -- C -> D (1), C -> E (5)
  let g := Graph.addAdjacencyList g "C" [{ target := "D", weight := some 1 }, { target := "E", weight := some 5 }]

  -- D -> A (10)
  let g := Graph.addAdjacencyList g "D" [{ target := "A", weight := some 10 }]

  -- E -> B (10), E -> F (1)
  let g := Graph.addAdjacencyList g "E" [{ target := "B", weight := some 10 }, { target := "F", weight := some 1 }]

  -- F -> B (1)
  let g := Graph.addAdjacencyList g "F" [{ target := "B", weight := some 1 }]

  -- Return the graph.
  g

def generateGraph04 : Graph :=
  -- Create an empty graph.
  let g : Graph := Graph.empty

  -- A -> B (1), A -> C (5)
  let g := Graph.addAdjacencyList g "A" [{ target := "B", weight := some 1 }, { target := "C", weight := some 5 }]

  -- B -> C (2)
  let g := Graph.addAdjacencyList g "B" [{ target := "C", weight := some 2 }]

  -- C
  let g := Graph.addAdjacencyList g "C" []

  -- D
  let g := Graph.addAdjacencyList g "D" []

  -- Return the graph.
  g

end Stuffs

open GraphDefinitions
open DijkstraUtils
open DijkstraAlgorithm
open Stuffs

-- Example usage of the graph and Dijkstra's algorithm.
def main : IO Unit := do
  -- Create an empty graph.
  let g : Graph := generateGraph02

  -- Print the graph.
  IO.println s!"Graph:\n{g}"

  -- Find the shortest paths from vertex "A".
  let shortestPaths := dijkstra g "A"

  -- Print the shortest paths.
  IO.println s!"Shortest paths from A:\n{shortestPaths}"

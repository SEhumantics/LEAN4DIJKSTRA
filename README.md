# Dijkstra's Algorithm in Lean 4

## Requirements

Prove the correctness and optimality of Dijkstra's algorithm for positive weighted graphs.

1. Model the positive weighted graph as a `Map` of `Vertex` to a list of `Edge` (a.k.a. adjacency list).
    - Checklist: DONE. See the `GraphDefinitions` namespace.

2. Implement Dijkstra's algorithm to find the shortest paths from a source vertex to all other vertices in the graph.
    - Checklist: DONE. See the `DijkstraUtils` and `DijkstraAlgorithm` namespaces.

3. Prove that:
    - The algorithm terminates.
        - Checklist: DONE. See the `termination_by` and `decreasing_by` annotations in the `dijkstraAuxiliary` function.
    - The algorithm finds the shortest paths in the graph.
        - Checklist: NOT DONE.

4. (Optional) Prove that if a negative weight cycle exists in the graph, the correctness of the algorithm won't be guaranteed.
    - Checklist: NOT DONE.

## Organization

The code is organized into several namespaces (and a main function at the end).

- The `GraphDefinitions` namespace contains the data structures to represent the graph, including the `Vertex`, `Weight`, and `Edge` types.

- The `DijkstraUtils` namespace contains utility data structures and functions for Dijkstra's algorithm, including the `Frontier` and `DistanceMap` types.

- The `DijkstraAlgorithm` namespace contains the implementation of Dijkstra's algorithm, including the `dijkstra` function.

- The `Stuffs` namespace contains some example graphs to test the algorithm.

- The `main` function demonstrates how to use the graph and Dijkstra's algorithm.

## Usage

To run the code, you can run the following command in the root directory of the project:

```lean
lean --run LEAN4DIJKSTRA/Graph.lean
```

To modify the graph, you can add your own `generateGraphXX` functions in the `Stuffs` namespace and call them in the `main` function, or modify the existing `generateGraphXX` functions.

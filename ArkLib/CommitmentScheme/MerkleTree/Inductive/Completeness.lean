/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.MerkleTree.Inductive.Defs

/-!
# Inductive Merkle Tree Completeness

-/


namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/--
A functional form of the completeness theorem for Merkle trees.
This references the functional versions of `getPutativeRoot` and `buildMerkleTree_with_hash`
-/
theorem functional_completeness (α : Type) {s : Skeleton}
  (idx : SkeletonLeafIndex s)
  (leaf_data_tree : LeafData α s)
  (hash : α → α → α) :
  (getPutativeRoot_with_hash
    idx
    (leaf_data_tree.get idx)
    (generateProof
      (buildMerkleTree_with_hash leaf_data_tree hash) idx)
    (hash)) =
  (buildMerkleTree_with_hash leaf_data_tree hash).getRootValue := by
  induction s with
  | leaf =>
    match leaf_data_tree with
    | LeafData.leaf a =>
      cases idx with
      | ofLeaf =>
        simp [buildMerkleTree_with_hash, getPutativeRoot_with_hash]
  | internal s_left s_right left_ih right_ih =>
    match leaf_data_tree with
    | LeafData.internal left right =>
      cases idx with
      | ofLeft idxLeft =>
        simp_rw [LeafData.get_ofLeft, LeafData.leftSubtree_internal, buildMerkleTree_with_hash,
          generateProof_ofLeft, FullData.rightSubtree, FullData.leftSubtree,
          getPutativeRoot_with_hash, left_ih, FullData.internal_getRootValue]
      | ofRight idxRight =>
        simp_rw [LeafData.get_ofRight, LeafData.rightSubtree_internal, buildMerkleTree_with_hash,
          generateProof_ofRight, FullData.leftSubtree, FullData.rightSubtree,
          getPutativeRoot_with_hash, right_ih, FullData.internal_getRootValue]


/--
Completeness theorem for Merkle trees.

The proof proceeds by reducing to the functional completeness theorem by a theorem about
the OracleComp monad,
and then applying the functional version of the completeness theorem.
-/
theorem completeness [DecidableEq α] [SampleableType α] {s}
    (leaf_data_tree : LeafData α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    NeverFail ((
      simulateQ randomOracle (do
        let cache ← buildMerkleTree leaf_data_tree
        let proof := generateProof cache idx
        let _ ← verifyProof idx (leaf_data_tree.get idx) (cache.getRootValue) proof)).run preexisting_cache :
      ProbComp (Unit × (spec α).QueryCache)) := by
  grind [buildMerkleTree, generateProof, verifyProof, getPutativeRoot,
    = HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

end InductiveMerkleTree

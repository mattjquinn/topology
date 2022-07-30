(* Proof for Exercise 1.1, #4 in "Topology Without Tears"
 * by Sidney A. Morris.
 *)
Require Import Omega.
Require Import Coq.Sets.Ensembles.

Local Open Scope nat_scope.

Definition Union_property (T : Ensemble (Ensemble nat)) : Prop :=
  (* TODO: for any subset of the powerset in which all elements belong to T, the union over all elements
     in that set must also be a member of T *)
  False.

Definition Intersection_property (T : Ensemble (Ensemble nat)) : Prop :=
  forall (T0 : Ensemble nat) (T1 : Ensemble nat),
    (In _ T T0) ->
    (In _ T T1) ->
    (In _ T (Intersection _ T0 T1)).


Definition T_is_topology_of_X (T : Ensemble (Ensemble nat)) (X : Ensemble nat) : Prop :=
  (* TODO: enforce T being a set of subsets, currently only set of sets. *)
  forall (T0: Ensemble (Ensemble nat)) (X0: Ensemble nat),
    (In _ T0 X0) ->
    (In _ T0 (Empty_set _)) ->
    (Intersection_property T) ->
    True.

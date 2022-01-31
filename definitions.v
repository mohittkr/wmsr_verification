Require Import Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra finset seq.
From GraphTheory Require Import digraph.
From Coquelicot Require Import Lim_seq Rbar.
From mathcomp.analysis Require Import Rstruct.
From Coq Require Import Logic.FunctionalExtensionality.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation diGraph := relType.
Notation di_edge := edge_rel.

(**** Define graph topology ******)

Variables (D: diGraph).

(** Define an F-paramter **)
Variable F:nat.


(** Define the vertex set **)
Definition Vertex : {set D}:= setT.


(** Define the set of advversary nodes **)
Definition Adversary (corrupt_choice:D -> bool):=
  [set x:D | corrupt_choice x == true].

(** Defines set of normal nodes **)
Definition Normal (corrupt_choice:D -> bool):=
  Vertex :\: Adversary corrupt_choice.


(** Define a set of in-neighbors :
  set of neighbors of i such that for any 
  j in the set, j--i is a valid edge relation in the 
  graph
**)
Definition in_neighbor (i:D) := [set j : D | j -- i].


(** Define the in-degree of i **)
Definition in_degree (i:D):= #|in_neighbor i|.

(** Define a set of out-neighbors:
  set of neigbors of i such that information 
  flows from i to j 
**)
Definition out_neighbor (i:D) := [set j:D | i -- j].

(** Define a set of inclusive neighbors:
  union of the set of in-neighbors and i itself **)
Definition inclusive_neigh (i:D) := 
   (in_neighbor i) :|: set1 i.


(** Define a r-reachable set **)
Definition r_reachable (r:nat) (S: {set D}):=
  S \proper Vertex /\ (#|S| > 0)%N /\
  (forall i:D, i \in S -> (#| (in_neighbor i) :\: S| >= r)%N).


(** Define a non-empty and non-trivial digraph **)
Definition nonempty_nontrivial_graph:= (#|D| >= 2)%N.

(** Define r-robustness **)
Definition r_robustness (r: nat):=
  nonempty_nontrivial_graph /\ 
  (forall (S1 S2: {set D}), 
      (S1 \proper Vertex /\ (#|S1|>0)%N) ->
      (S2 \proper Vertex /\ (#|S2|>0)%N) ->
      [disjoint S1 & S2] ->
      (r_reachable r S1 \/ r_reachable r S2)).
 
(** Define (r,s)-reachable set **)

(* Define Xi_S_r **)
Definition Xi_S_r (S: {set D}) (r:nat):= 
  [set i:D | i \in S & (#| (in_neighbor i) :\: S| >= r)%N].

(** Define (r,s)-reachability  **)
Definition r_s_reachable (S: {set D}) (r s:nat):=
  (S \proper Vertex /\ (#|S| > 0)%N) -> (#|Xi_S_r S r| >= s)%N.

(** Define (r,s)-robustness **)
Definition r_s_robustness (r s:nat):=
  nonempty_nontrivial_graph /\
  ( (1 <= s <= #|D|)%N ->
    forall (S1 S2: {set D}), 
      (S1 \proper Vertex /\ (#|S1|>0)%N) ->
      (S2 \proper Vertex /\ (#|S2|>0)%N) ->
      [disjoint S1 & S2] -> 
      ( (#|Xi_S_r S1 r| == #|S1|) || 
        (#|Xi_S_r S2 r| == #|S2|) ||
        (#|Xi_S_r S1 r| + #|Xi_S_r S2 r| >=s)%N )).

(*** Define the threat model and the W_MSR update ***)

Definition sorted_Dseq_rel (x: D -> R) (i j:D):=
if Rle_dec (x i) (x j) then if (x i == x j)%Re then
(index i (enum D) <= index j (enum D))%N else true
else false.
(**
if (x i == x j)%Re then (index i (enum D) < index j (enum D))%N else false.
**)
Definition sorted_seqD (l:seq D) (x:D -> R) :=
sort (sorted_Dseq_rel x) l.

Lemma pathP_D x p x0 (e:rel D) :
(forall i, (i < size p)%N -> e (nth x0 (x :: p) i) (nth x0 p i)) <->
(path e x p).
Proof.
split. intro. by apply /(pathP x0).
intro. by apply /pathP.
Qed.

(** define list of verticies **)
Definition inclusive_neighbor_list (i:D) (x:D -> R) := sort (sorted_Dseq_rel (x)) (enum (inclusive_neigh i)).

(** removes nodes in top F of list and greater than x t i or
in bottom F of list and less than x t i **)
Definition remove_extremes (i:D) (l:seq D) (x:D -> R) : (seq D) :=
  filter (fun (j:D) => (((Rge_dec (x j) (x i)) || (F <= (index j l))%N) &&
  ( Rle_dec (x j) (x i)  || (index j l <= ((size l) - F - 1))%N))) l.

(** gets inclusive neighbors of i and removes values **)
Definition incl_neigh_minus_extremes (i:D) (x:D -> R) : (seq D) :=
  remove_extremes i (inclusive_neighbor_list i x) x.

(** define the value of a node at time **)
Fixpoint x (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D) :=
  match (A i) with
  |true => mal t i
  |false =>
  (match t with
    | O => init i
    | S t' => sum_f_R0 (fun n:nat => let j :=
       (nth i (incl_neigh_minus_extremes i (x mal init A w t')) n) in
       (((x mal init A w t') j) * (w t' (i,j)))%Re) ((size (incl_neigh_minus_extremes i (x mal init A w t')))-1)
   end)
  end.


(** Defines the set of nodes, greater than
 x mal init A w t i, with values
in the top F of the inclusive_neighbor_list **)
Definition R_i_greater_than
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (i:D) (t:nat) :=
[set j | Rgt_dec ((x mal init A w t) j)
((x mal init A w t) i) &&
(index j (inclusive_neighbor_list i (x mal init A w t)) >
((size (inclusive_neighbor_list i (x mal init A w t))) - F - 1))%N &&
(j \in (inclusive_neighbor_list i (x mal init A w t)))].

(** Defines the set of nodes, greater than
 x mal init A w t i, with values
in the top F of the inclusive_neighbor_list, or potentially not in 
inclusive_neighbor_list **)
Definition R_i_greater_than_maybe_not_neighbors
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (i:D) (t:nat) :=
[set j | Rgt_dec ((x mal init A w t) j)
((x mal init A w t) i) &&
(index j (inclusive_neighbor_list i (x mal init A w t)) >
((size (inclusive_neighbor_list i (x mal init A w t))) - F - 1))%N].

(** Defines the set of nodes, less than
 x mal init A w t i, with values
in the top bottom of the inclusive_neighbor_list, or potentially not in 
inclusive_neighbor_list **)
Definition R_i_less_than_maybe_not_neighbors
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (i:D) (t:nat) :=
[set j | (Rlt_dec ((x mal init A w t) j)
((x mal init A w t) i)) &&
(index j (inclusive_neighbor_list i (x mal init A w t)) < F)%N].

(** Defines the set of nodes, less than
 x mal init A w t i, with values
in the bottom F of the inclusive_neighbor_list **)
Definition R_i_less_than
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (i:D) (t:nat) :=
[set j | (Rlt_dec ((x mal init A w t) j)
((x mal init A w t) i)) &&
(index j (inclusive_neighbor_list i (x mal init A w t)) < F)%N &&
(j \in (inclusive_neighbor_list i (x mal init A w t)))].

(** Defines condition for a node to have malicious behavior at a 
given time **)
Definition malicious_at_i_t
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (i:D) (t:nat): bool :=
(x mal init A w (t+1) i) != sum_f_R0 (fun n:nat =>
let j := (nth i (incl_neigh_minus_extremes i (x mal init A w t)) n) in
((x mal init A w t j) * (w t (i,j)))%Re) ((size (incl_neigh_minus_extremes i (x mal init A w t)))-1).

(** Define maliciousness **)
Definition malicious
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (i:D) := 
exists t:nat, malicious_at_i_t mal init A w i t.

(** defines condition for weights given in W-MSR at time t **)
Definition wts_well_behaved (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R) := 
exists a:R, (0<a)%Re /\ (a <1)%Re /\
(forall (t:nat) (i:D),
let incl := (incl_neigh_minus_extremes i (x mal init A w t)) in
(forall j:D, j \notin incl -> (w t (i,j) = 0)%Re) /\
(forall j:D, j \in incl ->(a <= w t (i,j)))%Re /\
sum_f_R0 (fun n:nat => let j := (nth i incl n) in
(w t (i,j))%Re) ((size incl)-1) = 1%Re).

(** Define an F_total set S **)
Definition F_total (S: {set D}) :=
  S \proper Vertex /\ (#|S| <= F)%N.

(** Define a F-totally bounded set of adversary nodes **)
Definition F_totally_bounded (A:D -> bool) :=
F_total (Adversary A).

(** Define an F-total malicious network **)
Definition F_total_malicious
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) :=
F_totally_bounded A /\
(forall i:D, i \in Adversary A -> malicious mal init A w i) /\
(forall j:D, j \in Normal A -> ~ (malicious mal init A w j)).

(** defines min and max values of normal nodes **)
Definition m (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat): R :=
  -(bigmaxr 0 ((map (fun i:D => -(x mal init A w t i)))
  (enum (Normal A)))).
Definition M (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat): R :=
  bigmaxr 0 (map (x mal init A w t) (enum (Normal A))).

(** defines resilient asymptotic consensus **)
Definition Resilient_asymptotic_consensus (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R):=
(F_total_malicious mal init A w) -> (exists L:Rbar,
forall (i:D), i \in (Normal A) ->
is_lim_seq (fun t: nat => x mal init A w t i) L) /\ 
(forall t:nat,  (m mal init A w 0 <= m mal init A w t)%Re /\
(M mal init A w t <= M mal init A w 0)%Re).

	(** we have to introduce a propositional completeness lemms	
    to reason classically. This is consistent with	
    the definition of prop_degeneracy from the Coq classical	
    facts library.	
 **)	
Axiom proposition_degeneracy : 	
  forall A:Prop, A = True \/ A = False.	
Lemma P_not_not_P: 	
  forall (P:Prop), P <->  ~(~ P).	
Proof.	
intros. split.	
+ intros. 	
  assert ( P = True \/ P = False).	
  { by apply proposition_degeneracy. }	
  destruct H0.	
  - by rewrite H0.	
  - by [].	
+ intros.	
  assert ( P = True \/ P = False).	
  { by apply proposition_degeneracy. }	
  destruct H0.	
  - by rewrite H0.	
  - contradict H. by rewrite H0.	
Qed. 

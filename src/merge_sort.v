(* begin hide *)
Require Import List.
Import ListNotations.
Require Import Recdef.
Require Import Arith.
Require Import Lia.
Require Import Sorted.
Require Import Permutation.
(* end hide *)

(** Neste trabalho formalizaremos a correção do algoritmo [mergesort]. Esta formalização envolve diversas etapas que incluem a definição de diferentes funções.  *)

(** O algoritmo [merge] a seguir recebe um par de listas ordenadas como argumento. A função [len] abaixo, define o tamanho de um par de listas: *)

Definition len (p:list nat * list nat) := length (fst p) + length (snd p).

Function merge (p: list nat * list nat) {measure len p}:=
  match p with
  | ([], l2) => l2
  | (l1, []) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
          if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
          else hd2 :: merge (l1, tl2)
  end.
Proof.
  - auto.
  - intros. unfold len. simpl. lia.
Qed.

Inductive ord: list nat -> Prop :=  
  | ord_nil: ord nil
  | ord_one: forall h, ord (h::nil)
  | ord_all: forall x y l, x <= y -> ord (y::l) -> ord (x::y::l).
  
Definition le_all x l := forall y, In y l -> x <= y.

Definition sorted_pair_lst (p: list nat * list nat) := ord (fst p) /\ ord (snd p).
     

Definition first_is_smallest (l : list nat) : Prop :=
  match l with
  | nil => True
  | hd :: tl => forall x, In x tl -> hd <= x
  end.



Function mergesort (l: list nat) {measure length l} :=
  match l with
  | [] => []
  | [h] => [h]
  | h1::h2::l' =>
      let l1_half := length(l)/2 in
      let l1 := firstn l1_half l in
      let l2 := skipn l1_half l in
      merge(mergesort l1 , mergesort l2)
  end.
  Proof.
  - intros. rewrite skipn_length. apply Nat.sub_lt.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
      * simpl. apply Nat.lt_0_succ.
        * apply Nat.lt_1_2.
      + apply Nat.div_str_pos. simpl. split.
      * apply Nat.lt_0_2.
        * apply Peano.le_n_S. apply Peano.le_n_S. apply Peano.le_0_n.  
    - intros. rewrite firstn_length. rewrite min_l.
    + apply Nat.div_lt.
      * simpl. apply Nat.lt_0_succ.
        * apply Nat.lt_1_2.
      + apply Nat.lt_le_incl. apply Nat.div_lt.
      * simpl. apply Nat.lt_0_succ.
        * apply Nat.lt_1_2.  
  Defined.


  Theorem sorted_implies_head_is_smallest : forall l, ord l -> first_is_smallest l.
  Proof. Admitted.

  Theorem tail_of_ord_l_is_sorted : forall (h1 : nat) (l1 : list nat), ord (h1 :: l1) -> ord l1.
  Proof. Admitted.
  
  Lemma in_merge : forall p x, In x (merge p) -> In x (fst p) \/ In x (snd p).
  Proof. Admitted.

  Lemma x_leq_all_in_l_implies_x_concat_l_is_sorted : forall x l, (forall y, In y l -> x <= y) -> ord l -> ord (x :: l).
  Proof. Admitted.

Theorem merge_ordena: forall p, sorted_pair_lst p -> ord (merge p).
  Proof.
    intros p [H1 H2]. 
    functional induction (merge p).
    - simpl. assumption.
    - simpl. assumption.
    - simpl in H1, H2, IHl. 
      assert(H3:=H1).
      apply tail_of_ord_l_is_sorted in H1.  
      apply sorted_implies_head_is_smallest in H3. unfold first_is_smallest in H3.
      specialize (IHl H1 H2).
      assert(H4:=H2).
      apply sorted_implies_head_is_smallest in H4.  unfold first_is_smallest in H4. 
      assert (H5 : forall x, In x tl2 -> hd1 <= x). {
      intros x HIn.
      specialize (H4 x HIn). 
      apply Nat.leb_le in e0.
      transitivity hd2; auto.
       }
      apply x_leq_all_in_l_implies_x_concat_l_is_sorted.
      intros y HIn. apply in_merge in HIn.  simpl in HIn.
      destruct HIn as [HIn_tl1 | [H_y_eq_hd2 | HIn_tl2]].
      + apply H3. assumption.
      + subst y. apply Nat.leb_le. assumption.
      + apply H5. assumption.
      + apply IHl.
    - simpl in H1, H2, IHl. 
      assert(H3:=H2).
      apply tail_of_ord_l_is_sorted in H2.  
      apply sorted_implies_head_is_smallest in H3. unfold first_is_smallest in H3.
      specialize (IHl H1 H2).
      assert(H4:=H1).
      apply sorted_implies_head_is_smallest in H4.  unfold first_is_smallest in H4.
      assert (H5 : forall x, In x tl1 -> hd2 <= x). {
        intros x HIn.
        specialize (H4 x HIn). 
        apply Nat.leb_nle in e0.
        transitivity hd2; auto.
        apply Nat.nle_gt in e0. 
        transitivity hd1.
       - apply Nat.lt_le_incl.
        assumption. 
       - assumption. 
       } 
       apply x_leq_all_in_l_implies_x_concat_l_is_sorted.
      intros y HIn. apply in_merge in HIn.  simpl in HIn.
      destruct HIn as [HIn_hd1_tl1 | HIn_tl2].
      destruct HIn_hd1_tl1 as [HIn_hd1_tl4 | HIn_tl5].
      + subst y. apply  Nat.leb_nle in e0. apply Nat.nle_gt in e0. 
        apply Nat.lt_le_incl in e0. assumption. 
      + apply H5. assumption.
      + apply H3. assumption.
      + apply IHl.

  Qed.



Theorem mergesort_correto: forall l, ord (mergesort l) /\ Permutation (mergesort l) l.
Proof. Admitted.


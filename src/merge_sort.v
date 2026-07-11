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
  
  Function split_l (l : list nat) : list nat * list nat :=
    match l with
    | nil => (nil, nil)
    | a :: nil => (a::nil, nil)
    | a :: (b :: t) => let x := split_l t in (a :: (fst x), b :: (snd x))
   end.
  
  
  Lemma merge_permuta: forall p, Permutation (merge p) (fst p ++ snd p).
  Proof.
    intros p.
    functional induction (merge p).
    - simpl.
      apply Permutation_refl. 
    - simpl.
      rewrite app_nil_r.
      apply Permutation_refl. 
    - simpl.
      apply Permutation_cons. 
      + reflexivity.
      + apply IHl.
    - simpl.
     apply Permutation_trans with (hd2 :: (fst (hd1 :: tl1, tl2) ++ snd (hd1 :: tl1, tl2))).
      + apply Permutation_cons.
        reflexivity.
        apply IHl.
      +  apply Permutation_middle.

  Qed.



  Lemma permutation_halve (l : list nat) :
    Permutation l (fst (split_l l) ++ snd (split_l l)).
  Proof.
    functional induction (split_l l); simpl; auto.
    apply perm_skip. apply perm_trans with (l' := (b :: snd (split_l t) ++ fst (split_l t))).
    - apply perm_skip. apply perm_trans with (l' := (fst (split_l t) ++ snd (split_l t))); auto.
      apply Permutation_app_comm.
    - rewrite app_comm_cons. apply Permutation_app_comm.
  Qed.


  Lemma mergesort_permuta: forall l, Permutation (mergesort l) l.
  Proof.
  intros l.
  functional induction (mergesort l).
  - apply Permutation_refl.
  - apply Permutation_refl.
  - simpl. rewrite merge_permuta.
  apply Permutation_trans with
    (firstn (fst (Nat.divmod (length l') 1 1 1)) (h1 :: h2 :: l') ++
     skipn  (fst (Nat.divmod (length l') 1 1 1)) (h1 :: h2 :: l')).
  + apply Permutation_app.
    * apply IHl0.
    * apply IHl1.
  + rewrite firstn_skipn. apply Permutation_refl.
Qed.


  Theorem sorted_implies_head_is_smallest : forall l, ord l -> first_is_smallest l.
  Proof.
    intros l H.
    induction H as [| h | x y l Hxy Hord IH].
    - unfold first_is_smallest.
      trivial.
    -  unfold first_is_smallest.
      intros x HIn.
      destruct HIn.
    -  unfold first_is_smallest.
      intros z HIn.
      destruct HIn as [Hz | HInTail].
        subst z.
        assumption.
        apply IH in HInTail.
        transitivity y; auto.
  Qed.

  Theorem tail_of_ord_l_is_sorted : forall (h1 : nat) (l1 : list nat), ord (h1 :: l1) -> ord l1.
  Proof.
     intros h1 l1 H.  
    induction l1 as [|h2 l2 IH].  
    - apply ord_nil.  
    - inversion H; subst. 
      assumption. 
  Qed.
  
  Lemma in_merge : forall p x, In x (merge p) -> In x (fst p) \/ In x (snd p).
  Proof.
    intros p x H.
    functional induction (merge p).
    -  simpl in H. right. assumption.
    - simpl in H. left. assumption.
    -  simpl in H. destruct H as [H | H].
        * left. left. assumption.
        * apply IHl in H. destruct H as [H | H].
          -- left. right. assumption.
          -- right. assumption.
      -  simpl in H. destruct H as [H | H].
        + right. left. assumption.
        + apply IHl in H. destruct H as [H | H].
          * left. assumption.
          * right. right. assumption.
  Qed.

  Lemma x_leq_all_in_l_implies_x_concat_l_is_sorted : forall x l, (forall y, In y l -> x <= y) -> ord l -> ord (x :: l).
  Proof.
    intros x l H_le H_ord.
    destruct l as [| hd tl].
    - apply ord_one. 
    -  constructor.
      +  apply H_le. 
        left. reflexivity. 
      + assumption.
  Qed.

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

Lemma  mergesort_ordena: forall l, ord (mergesort l).
  Proof.
  intros l.
  functional induction (mergesort l).
  -  apply ord_nil. 
  - apply ord_one.
  - apply merge_ordena.
    split; assumption.
Qed.

Theorem mergesort_correto: forall l, ord (mergesort l) /\ Permutation (mergesort l) l.
Proof.
  intros l.
  split.
  - apply mergesort_ordena.
  - apply mergesort_permuta.
Qed.


From Coq Require Import Arith.
(*Require Import Psatz.*)
(*Require Export Setoid Morphisms.*)
Import Coq.Lists.List.
Set Implicit Arguments.


Require Import Coq.Logic.FunctionalExtensionality.

Record fin X := {
  eq_dec : forall (a b : X), {a = b} + {a <> b};
  el : list X;
  all_el : forall a, List.In a el
  }.


Definition eq_bool A (Afin : fin A) x y := match (eq_dec Afin x y) with
  | left _ => true
  | right _ => false
  end.
  
Program Definition bool_fin : fin bool := {| el := cons true (cons false nil) |}.
Next Obligation. destruct a; destruct b. now left. now right. now right. now left. Qed.
Next Obligation. destruct a. now left. right. now left. Qed.


Section Finite.

Context {A B : Type} {Afin : fin A} {Bfin : fin B}.

Fixpoint build_set X (X_eq_dec : forall (a b : X), {a = b} + {a <> b}) (l : list X) : list (X -> bool) := match l with
    | nil => cons (fun _ => false) nil
    | a::q => let r := build_set X_eq_dec q in 
      (List.map (fun h b => match (X_eq_dec a b) with
        | left _ => false
        | right _ => h b
        end) r ++ 
      List.map (fun h b => match (X_eq_dec a b) with
        | left _ => true
        | right _ => h b
        end) r)
  end.

Lemma In_is_decidable : forall (l : list A) (a : A), {In a l} + {~ (In a l)}.
Proof. intros. pose proof (all_el Afin). induction l. right. intro. contradict H0.
  destruct (eq_dec Afin a a0). left. now left. destruct IHl. left. now right. right.
  Search (~ _ \/ _). intro. destruct H0. symmetry in H0. now contradict H0. now contradict H0.
Qed.

Definition Ffalse a := (fun (h : A -> bool) (b : A) =>
      if eq_dec Afin a b then false else h b).
      
Definition Ftrue a := (fun (h : A -> bool) (b : A) =>
      if eq_dec Afin a b then true else h b).

Program Definition funAbool : fin (A -> bool) := {| el := build_set (eq_dec Afin) (el Afin) |}.
Next Obligation. Check List.forallb.
  destruct (List.forallb (fun x => eq_bool bool_fin (a x) (b x)) (el Afin)) eqn : EQ.
  (*destruct (eq_dec bool_fin true (List.forallb (fun x => eq_bool bool_fin (a x) (b x)) (el Afin))).*)
  + left. apply functional_extensionality. rewrite forallb_forall in EQ.
  intro. specialize EQ with x. pose proof (all_el Afin). apply EQ in H. unfold eq_bool in H.
  Search (if _ then _ else _). destruct (eq_dec bool_fin (a x) (b x)) eqn : AB. assumption. contradict H.
  intuition.
  + right. intro. assert (forall x, a x = b x). intro. now rewrite H. contradict EQ. Search (_ <> false).
    apply Bool.not_false_iff_true. apply forallb_forall. intro x. intro. unfold eq_bool.
    destruct (eq_dec bool_fin (a x) (b x)). easy. contradict n. apply H0.
Qed.
Next Obligation. assert (forall l f, (forall x, f x = match In_is_decidable l x with 
  | left _ => f x
  | right _ => false
  end) -> In f (build_set (eq_dec Afin) l)).
  induction l; cbn. intros. left. apply functional_extensionality. intro.
  specialize H with x. destruct (In_is_decidable nil x). contradict i. now symmetry.
  intros. apply in_or_app. destruct (eq_dec bool_fin (f a0) true).
  + right. assert (f = (Ftrue a0 (fun x => match In_is_decidable l x with 
    | left _ => f x
    | right _ => false
    end))). apply functional_extensionality. intro. unfold Ftrue.
    destruct (eq_dec Afin a0 x). now rewrite <- e0.
    destruct (In_is_decidable l x). easy. specialize H with x.
    destruct (In_is_decidable (a0 :: l) x ). destruct i. now contradict H0. now contradict H0.
    assumption.
    
    rewrite H0. apply in_map. apply IHl. intros. now destruct (In_is_decidable l x).
  + left. assert (f = (Ffalse a0 (fun x => match In_is_decidable l x with 
    | left _ => f x
    | right _ => false
    end))). apply functional_extensionality. intro. unfold Ffalse.
    destruct (eq_dec Afin a0 x). rewrite <- e. destruct (f a0). contradict n. easy. easy.
    destruct (In_is_decidable l x). easy. specialize H with x.
    destruct (In_is_decidable (a0 :: l) x ). destruct i. now contradict H0. now contradict H0.
    assumption.
    
    rewrite H0. apply in_map. apply IHl. intros. now destruct (In_is_decidable l x).
  
  + apply H. intro. destruct (In_is_decidable (el Afin) x). easy. 
    contradict n. apply (all_el Afin).
Qed.
  



(*

  assert (forall x, a x = match In_is_decidable (el Afin) x with 
  | left _ => a x
  | right _ => false
  end). intros. destruct (In_is_decidable (el Afin) x). easy. contradict n. apply (all_el Afin).
  



 
   induction (el Afin).
  + cbn. left. apply functional_extensionality. intro. specialize H with x.
    destruct (In_is_decidable nil x). contradict i. now symmetry.
  + cbn in *. apply in_or_app. destruct (eq_dec bool_fin (a a0) false).
    - left. fold (Ffalse a0).
    assert (a = Ffalse a0 a). admit. rewrite H0. apply in_map. apply IHl. intros.
    specialize H with x. destruct (In_is_decidable (a0::l) x). destruct i.
    destruct (In_is_decidable l x). easy. now rewrite <- H1.
    destruct (In_is_decidable l x). easy. now contradict H1.
    destruct (In_is_decidable l x). easy. apply H.
    (*
     assert (In ((F a0) a)
  (map
    (F a0) (build_set (eq_dec Afin) l))). admit. apply H0.
    
    
    apply in_map.
    
     assert (a = ((fun (h : A -> bool) (b : A) =>
      if eq_dec Afin a0 b then false else h b) a)). admit.
      Search map. rewrite H0. apply in_map.*)
    - right. fold (Ftrue a0). assert (a = Ftrue a0 (fun x => (if In_is_decidable l x then a x else false))).
    admit. rewrite H0. apply in_map. apply IHl. intro.
    specialize H with x. destruct (In_is_decidable (a0::l) x). destruct i.
    destruct (In_is_decidable l x). easy. rewrite <- H1. apply IHl. now rewrite <- H1.
    destruct (In_is_decidable l x). easy. now contradict H1.
    destruct (In_is_decidable l x). easy. apply H.
*)

Print nil.

Definition empty C (Cfin : fin C) := (el Cfin = nil).

Definition empty_fun {C D} {Cfin : fin C} : @empty C Cfin -> (C -> D).
Proof. intros H x. pose proof (all_el Cfin). rewrite H in H0. contradict (H0 x). Qed.

Lemma empty_fun_ind_of_proof {C} {Cfin : fin C} (D : Type) : forall (H1 H2 : @empty C Cfin), 
  empty_fun (D := D) H1 = empty_fun H2.
  Proof. intros. apply functional_extensionality. intro. pose proof (all_el Cfin).
  rewrite H1 in H. contradict (H x). Qed.

Fixpoint add_last_image A B (A_eq_dec : forall (a b : A), {a = b} + {a <> b})
                            (B_eq_dec : forall (a b : B), {a = b} + {a <> b})
                            (l : list B) (previous_res : list (A -> option B)) (last_element : A)
                             : list (A -> option B) :=
  match l with
    | nil => nil
    | b :: q => List.map (fun h a => match (A_eq_dec last_element a) with
        | left _ => Some b
        | right _ => h a
        end) previous_res ++ add_last_image A_eq_dec B_eq_dec q previous_res last_element
  end.

Fixpoint build_fun_opt A B (A_eq_dec : forall (a b : A), {a = b} + {a <> b})
                       (B_eq_dec : forall (a b : B), {a = b} + {a <> b})
                       (lA : list A) (lB : list B) 
                       : list (A -> option B) 
    := match lA with
        | nil => cons (fun _ => None) nil
        | a::q => let r := build_fun_opt A_eq_dec B_eq_dec q lB in
                  add_last_image A_eq_dec B_eq_dec lB r a
        end.

Definition retrieve_option C D default (h : C -> option D) x := match (h x) with
                | None => default (* This case doesn't happen, just need the type to be correct *)
                | Some d0 => d0
                end.

(*
Program Definition build_fun C D (Cfin : fin C) (Dfin : fin D)
                       : list (C -> D)
  := match (el Dfin) with
    | nil => (match (el Cfin) as l return (el Cfin = l) -> list (C -> D) with
            | nil => (fun Heq =>  cons (@empty_fun C D Cfin Heq) nil)
            | c :: qc => fun _ => nil
            end) eq_refl
    | d :: qd => List.map (fun h x => match (h x) with
                | None => d (* This case doesn't happen, just need the type to be correct *)
                | Some d0 => d0
                end) (build_fun_opt (eq_dec Cfin) (eq_dec Dfin) (el Cfin) (el Dfin))
    end.*)
(*Next Obligation. unfold empty. symmetry. apply Heq_anonymous. Qed.*)

Program Definition build_fun C D (Cfin : fin C) (Dfin : fin D)
                       : list (C -> D)
  := match (el Dfin) with
    | nil => (match (el Cfin) as l return (el Cfin = l) -> list (C -> D) with
            | nil => (fun Heq =>  cons (@empty_fun C D Cfin Heq) nil)
            | c :: qc => fun _ => nil
            end) eq_refl
    | d :: qd => List.map (retrieve_option d) (build_fun_opt (eq_dec Cfin) (eq_dec Dfin) (el Cfin) (el Dfin))
    end.

Definition F_opt C im pre := (fun (h : A -> C) (a : A) =>
      if eq_dec Afin pre a then im else h a).


Program Definition funAB : fin (A -> B) := {| el := build_fun Afin Bfin |}.
Next Obligation. Check List.forallb.
  destruct (List.forallb (fun x => eq_bool Bfin (a x) (b x)) (el Afin)) eqn : EQ.
  (*destruct (eq_dec bool_fin true (List.forallb (fun x => eq_bool bool_fin (a x) (b x)) (el Afin))).*)
  + left. apply functional_extensionality. rewrite forallb_forall in EQ.
  intro. specialize EQ with x. pose proof (all_el Afin). apply EQ in H. unfold eq_bool in H.
  Search (if _ then _ else _). destruct (eq_dec Bfin (a x) (b x)) eqn : AB. assumption. contradict H.
  intuition.
  + right. intro. assert (forall x, a x = b x). intro. now rewrite H. contradict EQ. Search (_ <> false).
    apply Bool.not_false_iff_true. apply forallb_forall. intro x. intro. unfold eq_bool.
    destruct (eq_dec Bfin (a x) (b x)). easy. contradict n. apply H0.
Qed.
Next Obligation.
  induction (el Bfin) eqn : EQB.
  + induction (el Afin) eqn : EQA.
    - unfold build_fun. rewrite EQB. Check Eqdep_dec.UIP_dec.
      assert (empty Afin) as Em. apply EQA.
    (*pose proof (Eqdep_dec.UIP_dec).
    
      replace (match el Afin as l return (el Afin = l -> list (A -> B)) with
     | nil => fun Heq : el Afin = nil => empty_fun Heq :: nil
     | c :: qc => fun _ : el Afin = c :: qc => nil
     end eq_refl) with (empty_fun (D := B) Em :: nil). cbn. left.
     apply functional_extensionality. intro. pose proof (all_el Afin).
     rewrite EQA in H0. contradict (H0 x).

     
       assert ((fun (y : list A) (EQA0 : y = nil) =>
    empty_fun (Em) :: nil =
    (match y as l return (y = l -> list (A -> B)) with
    | nil => fun Heq : y = nil => empty_fun Em :: nil
    | c :: qc => fun _ : y = c :: qc => nil
    end eq_refl)) (el Afin) EQA). now rewrite EQA.

    cbn in H0.*)
    assert ((fun Heq : el Afin = nil => empty_fun (D := B) Heq :: nil) 
        =  (fun _ : el Afin = nil => empty_fun Em :: nil)).
    apply functional_extensionality. intro. apply f_equal2.
    apply empty_fun_ind_of_proof. reflexivity. rewrite H. rewrite EQA.
    assert (a = empty_fun Em). apply functional_extensionality. intro.
    pose proof (all_el Afin). rewrite EQA in H0. contradict (H0 x).
    rewrite H0. apply in_eq.

  (*
  apply H0. cbn.

     rewrite EQA. replace el0 with nil.
      case (el Afin). rewrite <- EQA.
  *)

    - pose proof (all_el Bfin). rewrite EQB in H. contradict (H (a a0)).

  +
  assert (forall l f, (forall x, match In_is_decidable l x with 
  | left _ => exists b, f x = Some b
  | right _ => f x = None
  end)
  -> In f (build_fun_opt (eq_dec Afin) (eq_dec Bfin) l (el Bfin))).
  induction l0; cbn.
  - intros. left. apply functional_extensionality. intro.
    specialize H with x. destruct (In_is_decidable nil x). contradict i. now symmetry.
  - intros. assert (f = (F_opt (f a1) a1 (fun x => match In_is_decidable l0 x with 
    | left _ => f x
    | right _ => None
    end))).
    apply functional_extensionality. intro. unfold F_opt.
    destruct (eq_dec Afin a1 x). now rewrite <- e.
    destruct (In_is_decidable l0 x). easy. specialize H with x.
    destruct (In_is_decidable (a1 :: l0) x). destruct i. now contradict H0.
    now contradict H0. assumption.
  
  
    assert (forall l_temp, (match f a1 with | Some b => In b l_temp |None => True end) ->  In f
     (add_last_image (eq_dec Afin) (eq_dec Bfin) l_temp
     (build_fun_opt (eq_dec Afin) (eq_dec Bfin) l0 (el Bfin)) a1)).
    ++
    induction l_temp. 
    * intro. pose proof (H a1). destruct (In_is_decidable (a1 :: l0) a1).
      destruct H2. rewrite H2 in H1. contradict H1.
      contradict n. apply in_eq.
    * intro. pose proof (H a1). destruct (In_is_decidable (a1 :: l0) a1).
      destruct H2. rewrite H2 in H1. destruct H1.
      ** unfold add_last_image. apply in_or_app. left.
        assert (F_opt (f a1) a1 = 
        (fun (h : A -> option B) (a3 : A) => if eq_dec Afin a1 a3 then Some a2 else h a3)).
        unfold F_opt. apply functional_extensionality. intro. apply functional_extensionality. intro.
        destruct (eq_dec Afin a1 x1). rewrite H2. now rewrite H1. easy.
        rewrite H0. rewrite <- H3. apply in_map. apply IHl0. intro. destruct (In_is_decidable l0 x0).
        pose proof (H x0). destruct (In_is_decidable (a1 :: l0) x0). apply H4. contradict n. now apply in_cons. easy.
      ** unfold add_last_image. apply in_or_app. right. apply IHl_temp. now rewrite H2.
     ** contradict n. apply in_eq.
    
    
    ++ apply H1. pose proof (H a1). destruct (In_is_decidable (a1 :: l0) a1).
      destruct H2. rewrite H2. apply (all_el Bfin). now rewrite H2.
    
    
   - unfold build_fun. rewrite EQB. assert (a = retrieve_option a0 (fun x => Some (a x))).
    apply functional_extensionality. intro. now cbn.
    rewrite H0. apply in_map. rewrite <- EQB. apply H. intro.
    destruct (In_is_decidable (el Afin) x). now exists (a x). contradict n. apply (all_el Afin).
   
   (*
    assert (a = (fun (h : A -> option B) (x : A) =>
      match h x as anonymous' return (anonymous' = h x -> B) with
      | Some d0 => fun _ : Some d0 = h x => d0
      | None => fun _ : None = h x => a0
      end eq_refl) (fun x => Some (a x))).
    
    
    
    
    
    
    destruct H with a1. now left. rewrite H3 in H2. inversion H2.
    unfold add_last_image. rewrite H1.
    Search app. apply in_or_app. left.
    
    assert (F_opt (f a1) a1 = 
      (fun (h : A -> option B) (a3 : A) => if eq_dec Afin a1 a3 then Some a2 else h a3)).
    admit.
    rewrite <- H5. apply in_map. unfold build_fun_opt. cbn. rewrite EQB. apply IHl_temp.
    
     unfold add_last_image. simpl. cbn. (*apply IHl_temp. assumption.*)
  
  
    rewrite H1. unfold add_last_image. (*unfold build_fun_opt. cbn.*)
    rewrite EQB. cbn. apply in_map.
     (* TODO *) apply in_map.
  
  
  
  
   apply in_or_app. destruct (eq_dec bool_fin (f a0) true).
  + right. assert (f = (Ftrue a0 (fun x => match In_is_decidable l x with 
    | left _ => f x
    | right _ => false
    end))). apply functional_extensionality. intro. unfold Ftrue.
    destruct (eq_dec Afin a0 x). now rewrite <- e0.
    destruct (In_is_decidable l x). easy. specialize H with x.
    destruct (In_is_decidable (a0 :: l) x ). destruct i. now contradict H0. now contradict H0.
    assumption.
    
    rewrite H0. apply in_map. apply IHl. intros. now destruct (In_is_decidable l x).
  + left. assert (f = (Ffalse a0 (fun x => match In_is_decidable l x with 
    | left _ => f x
    | right _ => false
    end))). apply functional_extensionality. intro. unfold Ffalse.
    destruct (eq_dec Afin a0 x). rewrite <- e. destruct (f a0). contradict n. easy. easy.
    destruct (In_is_decidable l x). easy. specialize H with x.
    destruct (In_is_decidable (a0 :: l) x ). destruct i. now contradict H0. now contradict H0.
    assumption.
    
    rewrite H0. apply in_map. apply IHl. intros. now destruct (In_is_decidable l x).
  
  + apply H. intro. destruct (In_is_decidable (el Afin) x). easy. 
    contradict n. apply (all_el Afin).*)
Qed.


End Finite.
  
  
  (*
  Fixpoint enumerate A (l : list A) (a : A) : nat :=
    match l with
      | nil => 0
      | a :: tl => 1
      | b :: tl => 1 + (enumerate A tl a)
    end.
  *)
  
  (*Search "list".*)
  
  (*
 Fixpoint build_set A (l : list A) (H : forall x, List.In x l) (n : nat) : (A -> B) := 
  match n with
    | 0 => 
  
 Fixpoint set_list A (l : list A) : list (A -> bool) := 
  match l with 
    | nil => nil
    | a :: tl => (fun x => a) :: (set_list tl)
  end.
  *)
  
  
  
  
  
  
  
  
  
  
  (* BROUILLON
  
  Définir les types finis dans un fichier à part comme ci-dessous
  
  Record fin X := {|
    eq_dec : forall a b, {a = b} + {a <> b};
    el : list A;
    all_ell : forall a, List.In a el
    |}.
    
  K = fin
  
  
  
  
  
  
  
  
  "list.filter" pour sélectionner selon une propriété --> autre chose
  
  match P a as b return P a = b -> (list {a | P a}) with
  | true => lambda H. [(a, H)]
  | false => lambda _ .[]
  end eq_refl.
  
  Rmq : proof irrelevance est vrai sur les booléens ! -> chercher le lemme associé !
  
  
  
  
  let rec f = function 
    | [] -> [lambda _ .false]
    | a::q -> let r = f q in List.map (lambda h b -> if a = b then false else h b) r ++ List.map (... true) r
    *)
  
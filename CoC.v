Require Import Arith.
Require Import Compare_dec.
Require Import Relations.
Require Import Extraction.

Inductive pseudoterm: Set :=
  | type
  | prop
  | bound (n: nat)
  | pi (t: pseudoterm) (b: pseudoterm)
  | lambda (t: pseudoterm) (b: pseudoterm)
  | application (f: pseudoterm) (x: pseudoterm).

Hint Constructors pseudoterm: coc.

Bind Scope coc_scope with pseudoterm.
Notation "\ t , b" := (lambda t b) (at level 190, format "\ t ,  b"): coc_scope.
Notation "\/ t , b" := (pi t b) (at level 190, format "\/ t ,  b"): coc_scope.
Notation "f @ x" := (application f x) (at level 150): coc_scope.
Coercion bound: nat >-> pseudoterm.

Inductive subterm: pseudoterm -> pseudoterm -> Prop :=
  | subterm_pi_left:
    forall t b, subterm t (pi t b)
  | subterm_pi_right:
    forall t b, subterm b (pi t b)
  | subterm_lambda_left:
    forall t b, subterm t (lambda t b)
  | subterm_lambda_right:
    forall t b, subterm b (lambda t b)
  | subterm_application_left:
    forall f x, subterm f (application f x)
  | subterm_application_right:
    forall f x, subterm x (application f x).

Hint Constructors subterm: coc.

Fixpoint lift (i: nat) (k: nat) (e: pseudoterm): pseudoterm :=
  match e with
  | type =>
    type
  | prop =>
    prop
  | bound n =>
    match le_gt_dec k n with
    | left _ => bound (i + n)
    | right _ => bound n
    end
  | pi t b =>
    pi (lift i k t) (lift i (S k) b)
  | lambda t b =>
    lambda (lift i k t) (lift i (S k) b)
  | application f x =>
    application (lift i k f) (lift i k x)
  end.

Lemma lift_zero_e_equals_e:
  forall e k,
  lift 0 k e = e.
Proof.
  induction e; auto with coc.
  - intro; unfold lift.
    destruct (le_gt_dec k n); reflexivity.
  - unfold lift in * |- *; intro.
    rewrite (IHe1 k).
    rewrite (IHe2 (S k)).
    reflexivity.
  - unfold lift in * |- *; intro.
    rewrite (IHe1 k).
    rewrite (IHe2 (S k)).
    reflexivity.
  - unfold lift in * |- *; intro.
    rewrite (IHe1 k).
    rewrite (IHe2 k).
    reflexivity.
Qed.

Hint Resolve lift_zero_e_equals_e: coc.

Lemma lift_distributes_over_pi:
  forall t b i k,
  lift i k (pi t b) = pi (lift i k t) (lift i (S k) b).
Proof.
  eauto with coc.
Qed.

Hint Resolve lift_distributes_over_pi: coc.

Lemma lift_distributes_over_lambda:
  forall t b i k,
  lift i k (lambda t b) = lambda (lift i k t) (lift i (S k) b).
Proof.
  eauto with coc.
Qed.

Hint Resolve lift_distributes_over_lambda: coc.

Lemma lift_distributes_over_application:
  forall f x i k,
  lift i k (application f x) = application (lift i k f) (lift i k x).
Proof.
  eauto with coc.
Qed.

Hint Resolve lift_distributes_over_application: coc.

Fixpoint subst (p: pseudoterm) (k: nat) (q: pseudoterm): pseudoterm :=
  match q with
  | type =>
    type
  | prop =>
    prop
  | bound n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => bound (pred n)
    | inleft (right _) => lift k 0 p
    | inright _ => bound n
    end
  | pi t b =>
    pi (subst p k t) (subst p (S k) b)
  | lambda t b =>
    lambda (subst p k t) (subst p (S k) b)
  | application f x =>
    application (subst p k f) (subst p k x)
  end.

Notation "q [ p /]" := (subst p 0 q) (at level 1, format "q [ p /]"): coc_scope.

Lemma subst_distributes_over_pi:
  forall t b i k,
  subst i k (pi t b) = pi (subst i k t) (subst i (S k) b).
Proof.
  eauto with coc.
Qed.

Hint Resolve subst_distributes_over_pi: coc.

Lemma subst_distributes_over_lambda:
  forall t b i k,
  subst i k (lambda t b) = lambda (subst i k t) (subst i (S k) b).
Proof.
  eauto with coc.
Qed.

Hint Resolve subst_distributes_over_lambda.

Lemma subst_distributes_over_application:
  forall f x i k,
  subst i k (application f x) = application (subst i k f) (subst i k x).
Proof.
  eauto with coc.
Qed.

Hint Resolve subst_distributes_over_application.

Inductive step: pseudoterm -> pseudoterm -> Prop :=
  | step_beta:
    forall t b x,
    step ((\t, b) @ x) (b[x/])
  | step_pi_left:
    forall t1 t2 b,
    step t1 t2 -> step (\/t1, b) (\/t2, b)
  | step_pi_right:
    forall t b1 b2,
    step b1 b2 -> step (\/t, b1) (\/t, b2)
  | step_lambda_left:
    forall t1 t2 b,
    step t1 t2 -> step (\t1, b) (\t2, b)
  | step_lambda_right:
    forall t b1 b2,
    step b1 b2 -> step (\t, b1) (\t, b2)
  | step_application_left:
    forall f1 f2 x,
    step f1 f2 -> step (f1 @ x) (f2 @ x)
  | step_application_right:
    forall f x1 x2,
    step x1 x2 -> step (f @ x1) (f @ x2).

Hint Constructors step: coc.
Notation "[ a => b ]" := (step a b): type_scope.

Definition star: pseudoterm -> pseudoterm -> Prop :=
  clos_refl_trans _ step.

Hint Unfold star: coc.
Hint Constructors clos_refl_trans: coc.
Notation "[ a =>* b ]" := (star a b): type_scope.

Lemma star_beta:
  forall t b x,
  [(\t, b) @ x =>* b[x/]].
Proof.
  auto with coc.
Qed.

Hint Resolve star_beta: coc.

Lemma star_step:
  forall a b,
  [a => b] -> [a =>* b].
Proof.
  auto with coc.
Qed.

Hint Resolve star_step: coc.

Lemma star_symm:
  forall a,
  [a =>* a].
Proof.
  auto with coc.
Qed.

Hint Resolve star_symm: coc.

Lemma star_tran:
  forall a b c,
  [a =>* b] -> [b =>* c] -> [a =>* c].
Proof.
  eauto with coc.
Qed.

Hint Resolve star_tran: coc.

Lemma star_pi_left:
  forall t1 t2 b,
  [t1 =>* t2] -> [\/t1, b =>* \/t2, b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_pi_left: coc.

Lemma star_pi_right:
  forall t b1 b2,
  [b1 =>* b2] -> [\/t, b1 =>* \/t, b2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_pi_right: coc.

Lemma star_lambda_left:
  forall t1 t2 b,
  [t1 =>* t2] -> [\t1, b =>* \t2, b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_lambda_left: coc.

Lemma star_lambda_right:
  forall t b1 b2,
  [b1 =>* b2] -> [\t, b1 =>* \t, b2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_lambda_right: coc.

Lemma star_application_left:
  forall f1 f2 x,
  [f1 =>* f2] -> [f1 @ x =>* f2 @ x].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_application_left: coc.

Lemma star_application_right:
  forall f x1 x2,
  [x1 =>* x2] -> [f @ x1 =>* f @ x2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_application_right: coc.

Definition conv: pseudoterm -> pseudoterm -> Prop :=
  clos_refl_sym_trans _ step.

Hint Unfold conv: coc.
Hint Constructors clos_refl_sym_trans: coc.
Notation "[ a <=> b ]" := (conv a b): type_scope.

Lemma conv_beta:
  forall t b x,
  [(\t, b) @ x <=> b[x/]].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_beta: coc.

Lemma conv_step:
  forall a b,
  [a => b] -> [a <=> b].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_step: coc.

Lemma conv_star:
  forall a b,
  [a =>* b] -> [a <=> b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_star: coc.

Lemma conv_refl:
  forall a,
  [a <=> a].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_refl: coc.

Lemma conv_tran:
  forall a b c,
  [a <=> b] -> [b <=> c] -> [a <=> c].
Proof.
  eauto with coc.
Qed.

Hint Resolve conv_tran: coc.

Lemma conv_symm:
  forall a b,
  [a <=> b] -> [b <=> a].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_symm: coc.

Lemma subterm_and_step_commute:
  commut _ subterm (transp _ step).
Proof.
  induction 1; compute; eauto with coc.
Qed.

Hint Unfold transp: coc.

Definition normal (a: pseudoterm): Prop :=
  forall b, ~[a => b].

Definition strongly_normalizing: pseudoterm -> Prop :=
  Acc (transp _ step).

Lemma subterm_of_normalizing_is_normalizing:
  forall a,
  strongly_normalizing a ->
  forall b,
  subterm b a -> strongly_normalizing b.
Proof.
  compute.
  simple induction 1.
  intros.
  constructor.
  intros.
  edestruct subterm_and_step_commute; eauto.
Qed.

Inductive parallel: pseudoterm -> pseudoterm -> Prop :=
  | parallel_beta:
    forall t b1 b2 x1 x2,
    parallel b1 b2 -> parallel x1 x2 -> parallel ((\t, b1) @ x1) (b2[x2/])
  | parallel_type:
    parallel type type
  | parallel_prop:
    parallel prop prop
  | parallel_bound:
    forall n, parallel (bound n) (bound n)
  | parallel_pi:
    forall t1 t2 b1 b2,
    parallel t1 t2 -> parallel b1 b2 -> parallel (\/t1, b1) (\/t2, b2)
  | parallel_lambda:
    forall t1 t2 b1 b2,
    parallel t1 t2 -> parallel b1 b2 -> parallel (\t1, b1) (\t2, b2)
  | parallel_application:
    forall f1 f2 x1 x2,
    parallel f1 f2 -> parallel x1 x2 -> parallel (f1 @ x1) (f2 @ x2).

Hint Constructors parallel: coc.

Lemma parallel_refl:
  forall e,
  parallel e e.
Proof.
  simple induction e; auto with coc.
Qed.

Hint Resolve parallel_refl: coc.

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
Proof.
  induction 1; auto with coc.
Qed.

Hint Resolve parallel_step: coc.

Lemma star_parallel:
  forall a b,
  parallel a b -> [a =>* b].
Proof.
  simple induction 1; eauto with coc.
  - intros.
    eapply star_tran.
    eapply star_tran.
    apply star_application_left.
    apply star_lambda_right.
    exact H1.
    apply star_application_right.
    exact H3.
    apply star_beta.
Qed.

Hint Resolve star_parallel: coc.

Lemma lift_addition_distributes_over_subst:
  forall a b n p k,
  lift n (p + k) (subst b p a) = subst (lift n k b) p (lift n (S (p + k)) a).
Proof.
  induction a; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: bound. *)
  - admit.
  (* Case: pi. *)
  - simpl; f_equal.
    + apply IHa1.
    + replace (S (p + k)) with (S p + k).
      apply IHa2.
      auto.
  (* Case: lambda. *)
  - simpl; f_equal.
    + apply IHa1.
    + replace (S (p + k)) with (S p + k).
      apply IHa2.
      auto.
  (* Case: application. *)
  - simpl; f_equal.
    + apply IHa1.
    + replace (S (p + k)) with (S p + k).
      apply IHa2.
      auto.
Admitted.

Lemma lift_distributes_over_subst:
  forall a b i k,
  lift i k (subst b 0 a) = subst (lift i k b) 0 (lift i (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply lift_addition_distributes_over_subst.
Qed.

Lemma subst_distributes_over_itself:
  forall P N M k,
  subst P k (subst N 0 M) = subst (subst P k N) 0 (subst P (S k) M).
Proof.
(* XXX *)
Admitted.

Lemma parallel_lift:
  forall a b,
  parallel a b ->
  forall i k,
  parallel (lift i k a) (lift i k b).
Proof.
  simple induction 1.
  - intros.
    rewrite lift_distributes_over_application.
    rewrite lift_distributes_over_lambda.
    rewrite lift_distributes_over_subst.
    auto with coc.
  - auto with coc.
  - auto with coc.
  - auto with coc.
  - intros.
    do 2 rewrite lift_distributes_over_pi.
    auto with coc.
  - intros.
    do 2 rewrite lift_distributes_over_lambda.
    auto with coc.
  - intros.
    do 2 rewrite lift_distributes_over_application.
    auto with coc.
Qed.

Hint Resolve parallel_lift: coc.

Lemma parallel_subst:
  forall a b,
  parallel a b ->
  forall c d,
  parallel c d ->
  forall k,
  parallel (subst c k a) (subst d k b).
Proof.
  simple induction 1.
  - intros.
    rewrite subst_distributes_over_application.
    rewrite subst_distributes_over_lambda.
    rewrite subst_distributes_over_itself.
    auto with coc.
  - auto with coc.
  - auto with coc.
  - intros.
    unfold subst.
    destruct (lt_eq_lt_dec k n) as [ [ _ | _ ] | _ ]; auto with coc.
  - intros.
    do 2 rewrite subst_distributes_over_pi.
    auto with coc.
  - intros.
    do 2 rewrite subst_distributes_over_lambda.
    auto with coc.
  - intros.
    do 2 rewrite subst_distributes_over_application.
    auto with coc.
Qed.

Hint Resolve parallel_subst: coc.

Definition confluent {T} (R: T -> T -> Prop): Prop :=
  commut _ R (transp _ R).

Lemma parallel_is_confluent:
  confluent parallel.
Proof.
  compute.
  induction 1.
  (* Case: parallel_beta. *)
  - intros.
    inversion_clear H1.
    + destruct (IHparallel1 _ H2) as (b4, ?, ?).
      destruct (IHparallel2 _ H3) as (x4, ?, ?).
      exists (subst x4 0 b4); auto with coc.
    + inversion_clear H2.
      destruct (IHparallel1 _ H4) as (b4, ?, ?).
      destruct (IHparallel2 _ H3) as (x4, ?, ?).
      exists (subst x4 0 b4); auto with coc.
  (* Case: parallel_type. *)
  - intros.
    inversion_clear H.
    exists type; auto with coc.
  (* Case: parallel_prop. *)
  - intros.
    inversion_clear H.
    exists prop; auto with coc.
  (* Case: parallel_bound. *)
  - intros.
    inversion_clear H.
    exists n; auto with coc.
  (* Case: parallel_pi. *)
  - intros.
    inversion_clear H1.
    destruct (IHparallel1 _ H2) as (t4, ?, ?).
    destruct (IHparallel2 _ H3) as (b4, ?, ?).
    exists (pi t4 b4); auto with coc.
  (* Case: parallel_lambda. *)
  - intros.
    inversion_clear H1.
    destruct (IHparallel1 _ H2) as (t4, ?, ?).
    destruct (IHparallel2 _ H3) as (b4, ?, ?).
    exists (lambda t4 b4); auto with coc.
  (* Case: parallel_application. *)
  - intros.
    inversion H1.
    + destruct H3, H2, H5.
      rename t into t1, x0 into x1, b2 into b3.
      inversion H.
      destruct H2, H3, H7.
      rename t0 into t1, b0 into b1.
      edestruct IHparallel1.
      apply parallel_lambda.
      apply parallel_refl.
      exact H4.
      rename x into f4.
      inversion H2.
      destruct H7, H9, H11.
      rename t0 into t2, b0 into b2.
      inversion H3.
      destruct H7, H9, H11, H14.
      rename t0 into t1, b0 into b3, b5 into b4.
      destruct (IHparallel2 _ H6) as (x4, ?, ?).
      exists (subst x4 0 b4); eauto with coc.
    + destruct H2, H3, H5.
      destruct (IHparallel1 _ H4) as (f4, ?, ?).
      destruct (IHparallel2 _ H6) as (x4, ?, ?).
      exists (application f4 x4); auto with coc.
Qed.

Lemma strip_lemma {T} (R: T -> T -> Prop):
  confluent R -> commut _ (clos_trans _ R) (transp _ R).
Proof.
  simple induction 2; intros.
  - elim H with z x0 y0; eauto with sets.
  - elim H2 with z0; auto with sets; intros.
    elim H4 with x1; auto with sets; intros.
    eexists; eauto with sets.
    eapply t_trans; eauto.
Qed.

Lemma transitive_closure_of_confluent_is_confluent {T} (R: T -> T -> Prop):
  confluent R -> confluent (clos_trans _ R).
Proof.
  intro confluency.
  unfold confluent, commut, transp.
  simple induction 1; intros.
  destruct (strip_lemma R) with z x0 y0; auto.
  - eauto with sets.
  - elim H1 with z0; auto; intros.
    elim H3 with x1; auto; intros.
    exists x2; auto.
    eapply t_trans; eauto.
Qed.

Lemma transitive_parallel_is_confluent:
  confluent (clos_trans _ parallel).
Proof.
  apply transitive_closure_of_confluent_is_confluent.
  exact parallel_is_confluent.
Qed.

Lemma transitive_parallel_star:
  forall a b,
  [a =>* b] -> clos_trans _ parallel a b.
Proof.
  simple induction 1.
  - auto with coc sets.
  - auto with coc sets.
  - intros; eapply t_trans; eauto.
Qed.

Lemma star_transitive_parallel:
  forall a b,
  clos_trans _ parallel a b -> [a =>* b].
Proof.
  induction 1; eauto with coc.
Qed.

Lemma star_is_confluent:
  confluent star.
Proof.
  unfold confluent, commut, transp.
  intros.
  elim transitive_parallel_is_confluent with x y z.
  - compute; intros.
    exists x0.
    apply star_transitive_parallel; auto.
    apply star_transitive_parallel; auto.
  - eapply transitive_parallel_star; auto.
  - eapply transitive_parallel_star; auto.
Qed.

Definition church_rosser {T} (R: T -> T -> Prop): Prop :=
  forall a b,
  clos_refl_sym_trans T R a b ->
  exists2 c: T, clos_refl_trans T R a c & clos_refl_trans T R b c.

Lemma confluency_implies_church_rosser {T} (R: T -> T -> Prop):
  confluent (clos_refl_trans _ R) -> church_rosser R.
Proof.
  simple induction 2; intros.
  (* Case: step. *)
  - eauto with sets.
  (* Case: refl. *)
  - eauto with sets.
  (* Case: symm. *)
  - destruct H2 as (z, ?, ?).
    exists z; auto.
  (* Case: tran. *)
  - destruct H2 as (c, ?, ?).
    destruct H4 as (d, ?, ?).
    destruct H with c y d as (e, ?, ?); auto.
    exists e; eapply rt_trans; eauto.
Qed.

Theorem step_is_church_rosser:
  church_rosser step.
Proof.
  apply confluency_implies_church_rosser.
  exact star_is_confluent.
Qed.

(******************************************************************************)

Lemma inversion_star_normal:
  forall a b,
  [a =>* b] -> normal a ->
  forall P: Prop,
  (a = b -> P) -> P.
Proof.
  simple induction 1; intros.
  (* Case: step. *)
  - absurd (step x y); auto.
  (* Case: refl. *)
  - auto.
  (* Case: tran. *)
  - apply H1.
    assumption.
    intro.
    destruct H6.
    apply H3; auto.
Qed.

Lemma normal_form_is_unique:
  forall a b,
  [a <=> b] -> normal a -> normal b -> a = b.
Proof.
  intros.
  destruct step_is_church_rosser with a b.
  - assumption.
  - apply inversion_star_normal with a x;
      apply inversion_star_normal with b x;
      auto.
    congruence.
Qed.

(******************************************************************************)

Definition context: Set :=
  list pseudoterm.

Inductive item (e: pseudoterm): context -> nat -> Prop :=
  | item_car:
    forall cdr, item e (cons e cdr) 0
  | item_cdr:
    forall car cdr n, item e cdr n -> item e (cons car cdr) (S n).

Definition item_lift g e n: Prop :=
  exists2 x, e = lift (S n) 0 x & item x g n.

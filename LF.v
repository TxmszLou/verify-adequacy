Require String Fin Vector Bool.
Require Import List Nat.
Require Import Omega.
Import ListNotations.

From StructTact Require Import StructTactics Assoc.

(* Tactic for inverting equalities between dependent pairs where the first
   component has type nat. *)
Ltac inv_existT := repeat match goal with
| [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
  apply Eqdep_dec.inj_pair2_eq_dec in H; [| solve [auto using PeanoNat.Nat.eq_dec]]
end; subst.


(* setup vector notations *)
Arguments Vector.nil {_}.
Arguments Vector.cons {_} _ {_} _.

Delimit Scope vector_scope with vector.
Delimit Scope string_scope with string.
Bind Scope vector_scope with Vector.t.

Notation "[ ]" := Vector.nil : vector_scope.
Notation "h :: t" := (Vector.cons h t) (at level 60, right associativity) : vector_scope.
Notation " [ x ] " := (Vector.cons x []) : vector_scope.
Notation " [ x ; y ; .. ; z ] " := (x :: (y :: .. (z :: []) ..))%vector : vector_scope.

Open Scope vector_scope.

Set Implicit Arguments.

Module member.

  Inductive t {A : Type} (elm : A) : list A -> Type :=
  | Here  : forall l, t elm (elm :: l)
  | There : forall a l, t elm l -> t elm (a :: l)
  .

  (* case schemes *)
  Arguments Here {_ _ _}.
  Arguments There {_ _ _ _} _.

  
  Definition case_nil {A} (a : A) {P : Type} (m : t a []) : P :=
    match m with
    | Here => I
    | There m => I
    end.

  Definition case_cons {A} {a : A} {l} (P : forall a0, t a (a0 :: l) -> Type)
             (PHere : P _ Here)
             (PThere : forall a0 m, P a0 (There m))
             {a0} (m : t a (a0 :: l)) : P a0 m.
    revert P PHere PThere.
    refine match m with
           | Here => _
           | There m => _
           end; auto.
  Defined.
End member.

(**
Module hlist.
  Local Open Scope list.

  (** hlist for implementing constant context *)

  Inductive t {A : Type} (B : A -> Type) : list A -> Type :=
  | nil  : t B []
  | cons : forall a (b : B a) l (h : t B l), t B (a :: l)
  .

  Arguments nil {_ _}.
  Arguments cons {_ _ _} _ {_} _.

  Delimit Scope hlist_scope with hlist.
  Bind Scope hlist_scope with hlist.t.

  Local Notation "[ ]" := nil : hlist_scope.
  Local Notation "h :: t" := (cons h t) (at level 60, right associativity) : hlist_scope.
  Local Notation " [ x ] " := (x :: [])%hlist : hlist_scope.
  Local Notation " [ x ; y ; .. ; z ] " := (x :: (y :: .. (z :: []) ..))%hlist : hlist_scope.

  Local Open Scope hlist_scope.

  Fixpoint get {A} {B : A -> Type} {l} (h : t B l) {a} {struct h} : member.t a l -> B a.
    refine match h with
           | [] => fun m => member.case_nil m
           | b :: h => fun m => _
           end.
    destruct a0, m using member.case_cons.
    - exact b.
    - exact (get _ _ _ h _ m).
  Defined.

  (* helper functions on hlist *)

  Fixpoint any {A} {B : A -> Type} {l} (h : t B l) (f : forall a, B a -> bool) {struct h} : bool.
    refine match h with
           | [] => false
           | b :: h => _
           end.
    exact (if f _ b then true else any _ _ _ h f).
  Defined.

  Module notations.
    Delimit Scope hlist_scope with hlist.
    Bind Scope hlist_scope with hlist.t.

    Notation "[ ]" := nil : hlist_scope.
    Notation "h :: t" := (cons h t) (at level 60, right associativity) : hlist_scope.
    Notation " [ x ] " := (x :: [])%hlist : hlist_scope.
    Notation " [ x ; y ; .. ; z ] " := (x :: (y :: .. (z :: []) ..))%hlist : hlist_scope.
  End notations.

  Module member.
    Check t.
    Inductive m {A : Type} {B : A -> Type} {a : A} (b : B a) : forall l, t B l -> Type :=
    | Here  : forall l (h : t B l), m b (b :: h)
    | There : forall l (h : t B l) {c} (x : B c), m b h -> m b (x :: h)
    .

    Arguments m {_ _ _} _ {_} _.
    Arguments Here {_ _ _ _ _ _}.
    Arguments There {_ _ _ _ _ _ _ _} _.
  End member.
  
End hlist. *)

(** LF implemented in Coq *)

(** a) LF type theory *)

Definition vtest := [2;2;5;4].
Eval compute in Vector.nth vtest (Fin.FS Fin.F1).

Module LF.
  (* traditional LF (cf. Harper, Honsell, Plotkin) *)
  Module guid.
    Definition t := String.string.
    Definition eq_dec : forall x y, {x = y} + {x <> y} := String.string_dec.
  End guid.

  Module expr.
    Inductive t : nat -> Type :=
    | KType : forall {n}, t n
    | KPi   : forall n, t n -> t (S n) -> t n
    | TyConst : forall {n}, guid.t -> t n
    | TyPi    : forall n, t n -> t (S n) -> t n
    | TyLam   : forall n, t (S n) -> t n
    | TyApp   : forall n, t n -> t n -> t n
    | TmConst : forall {n}, guid.t -> t n
    | TmVar   : forall n, Fin.t n -> t n
    | TmLam   : forall n, t (S n) -> t n
    | TmApp   : forall n, t n -> t n -> t n
    .

    (** operations on syntax *)
    (* lifting *)
    Fixpoint lift_fin (c : nat) {n} (f : Fin.t n) : Fin.t (S n) :=
      match c with
      | 0 => Fin.FS f
      | S c' => match f with
               | Fin.F1 => Fin.F1
               | Fin.FS f => Fin.FS (lift_fin c' f)
               end
      end.

    Fixpoint lift (c : nat) {n} (e : t n) : t (S n) :=
      match e with
      | KType => KType
      | KPi A K => KPi (lift c A) (lift c K)
      | TyConst k => TyConst k
      | TyPi A B  => TyPi (lift c A) (lift c B)
      | TyLam B   => TyLam (lift (S c) B)
      | TyApp A M => TyApp (lift c A) (lift c M)
      | TmConst k => TmConst k
      | TmVar f => TmVar (lift_fin c f)
      | TmLam M => TmLam (lift (S c) M)
      | TmApp M N => TmApp (lift c M) (lift c N)
      end.

    (* lift variables by k *)
    Fixpoint lift_k (k c : nat) {n} (e : t n) : t (n + k).
      refine match k with
             | 0 => _
             | S k => _
             end.
      - assert (n + 0 = n) by omega. rewrite H; exact e.
      - rewrite <- plus_Snm_nSm. exact (lift_k k c (S n) (lift c e)).
    Defined.
    
    (* multisubstitution *)
    Fixpoint subst {n} (e : t n) {n'} : Vector.t (t n') n -> t n' :=
      let rec_bind {n} (e : t (S n)) {n'} (v : Vector.t (t n') n) :=
          subst e (TmVar Fin.F1 :: Vector.map (lift 0) v) in
      match e with
      | KType => fun _ => KType
      | KPi A K => fun v => KPi (subst A v) (rec_bind K v)

      | TyConst k => fun _ => TyConst k
      | TyPi A B => fun v => TyPi (subst A v) (rec_bind B v)
      | TyLam B => fun v => TyLam (rec_bind B v)
      | TyApp A M => fun v => TyApp (subst A v) (subst M v)

      | TmConst k => fun _ => TmConst k
      | TmVar f => fun v => Vector.nth v f
      | TmLam M => fun v => TmLam (rec_bind M v)
      | TmApp M N => fun v => TmApp (subst M v) (subst N v)
      end.

    Fixpoint identity_subst (n : nat) : Vector.t (t n) n :=
      match n with
      | 0 => []
      | S n => TmVar Fin.F1 :: Vector.map (lift 0) (identity_subst n)
      end.


    (* recursion on closed terms *)
    Section rec0.
      Variable P : t 0 -> Type.
      Hypothesis PKType : P KType.
      Hypothesis PKPi   : forall a k, P a -> P (KPi a k).

      Hypothesis PTyConst : forall k, P (TyConst k).
      Hypothesis PTyPi   : forall a b, P a -> P (TyPi a b).
      Hypothesis PTyLam  : forall b, P (TyLam b).
      Hypothesis PTyApp   : forall a m, P a -> P m -> P (TyApp a m).

      Hypothesis PTmConst : forall k, P (TmConst k).
      Hypothesis PTmLam   : forall m, P (TmLam m).
      Hypothesis PTmApp   : forall m n, P m -> P n -> P (TmApp m n).


      Fixpoint rec0 (e : expr.t 0) : P e.
        refine match e with
              | KType => _
              | KPi a k => _
              | TyConst k => _
              | TyPi a b => _
              | @TyLam n b => _
              | TyApp a m => _
              | TmConst k => _
              | TmVar f => _
              | @TmLam n m => _
              | TmApp p m => _
              end; destruct n; try exact (fun A x => x).
        - apply PKType.
        - apply PKPi; apply rec0.
        - apply PTyConst.
        - apply PTyPi; apply rec0.
        - apply PTyLam.
        - apply PTyApp; apply rec0.
        - apply PTmConst.
        - destruct f using Fin.case0.
        - apply PTmLam.
        - apply PTmApp; apply rec0.
      Defined.
    End rec0.

    (* A case analysis scheme for _closed_ terms *)
    Definition case0 (P : t 0 -> Type)
      (PKType : P KType)
      (PKPi   : forall a k, P (KPi a k))
      (PTyConst : forall k, P (TyConst k))
      (PTyPi  : forall a2 a, P (TyPi a2 a))
      (PTyLam : forall b, P (TyLam b))
      (PTyApp   : forall p m, P (TyApp p m))
      (PTmConst : forall k, P (TmConst k))
      (PTmLam   : forall m, P (TmLam m))
      (PTmApp   : forall r m, P (TmApp r m))
      : forall e, P e :=
      rec0 P
           PKType
           (fun a k _ => PKPi a k)
           PTyConst
           (fun a2 a _ => PTyPi a2 a)
           (fun b => PTyLam b)
           (fun p m _ _ => PTyApp p m)
           PTmConst
           PTmLam
           (fun r m _ _ => PTmApp r m)
    .
    
    (* Equality decider : modified from MiniPRL *)
    Fixpoint eq_dec {n} (e1 : t n) : forall e2 : t n, {e1 = e2} + {e1 <> e2}.
      refine match e1 in t n0 return forall e2 : t n0, _ with
             | KType    => fun e2 =>
                match e2 as e2' return {KType = e2'}  + {KType <> e2'} with
                | KType    => left _
                | _        => right _
                end
             | KPi A1 K1 => fun e2 =>
                match e2 as e2' return forall A1 K1, {KPi A1 K1 = e2'} + {KPi A1 K1 <> e2'} with
                | KPi A2 K2 => fun A1 K1 =>
                                match eq_dec _ A1 A2 with
                                | left _ =>
                                  match eq_dec _ K1 K2 with
                                  | left _ => left _
                                  | right _ => right _
                                  end
                                | right _ => right _
                                end
                | _ => fun _ _ => right _
                end A1 K1
             | TyConst k1 => fun e2 =>
                match e2 as e2' return {TyConst k1 = e2'} + {TyConst k1 <> e2'} with
                | TyConst k2 =>
                  match guid.eq_dec k1 k2 with
                  | left _ => left _
                  | right _ => right _
                  end
                | _ => right _
                end
             | TyPi A12 A1 => fun e2 =>
                match e2 as e2' return forall A12 A1, {TyPi A12 A1 = e2'} + {TyPi A12 A1 <> e2'} with
                | TyPi A22 A2 => fun A12 A1 =>
                                  match eq_dec _ A12 A22 with
                                  | left _ =>
                                    match eq_dec _ A1 A2 with
                                    | left _ => left _
                                    | right _ => right _
                                    end
                                  | right _ => right _
                                  end
                | _ => fun A12 A1 => right _
                end A12 A1
             | TyLam B1 => fun e2 =>
                match e2 as e2' return forall B1, {TyLam B1 = e2'} + {TyLam B1 <> e2'} with
                | TyLam B2 => fun B1 =>
                                match eq_dec _ B1 B2 with
                                | left _ => left _
                                | right _ => right _
                                end
                | _ => fun _ => right _
                end B1
             | TyApp P1 M1 => fun e2 =>
                match e2 as e2' return forall P1 M1, {TyApp P1 M1 = e2'} + {TyApp P1 M1 <> e2'} with
                | TyApp P2 M2 => fun P1 M1 =>
                                  match eq_dec _ P1 P2 with
                                  | left _ =>
                                    match eq_dec _ M1 M2 with
                                    | left _ => left _
                                    | right _ => right _
                                    end
                                  | right _ => right _
                                  end
                | _ => fun _ _ => right _
                end P1 M1
             | TmConst k1   => fun e2 =>
                match e2 as e2' return {TmConst k1 = e2'} + {TmConst k1 <> e2'} with
                | TmConst k2 =>
                  match guid.eq_dec k1 k2 with
                  | left _ => left _
                  | right _ => right _
                  end
                | _ => right _
                end
             | TmVar x      => fun e2 =>
                match e2 as e2' in t n0 return forall x : Fin.t n0, {TmVar x = e2'} + {TmVar x <> e2'} with
                | TmVar y => fun x =>
                              match Fin.eq_dec x y with
                              | left _ => left _
                              | right _ => right _
                              end
                | _ => fun _ => right _
                end x
             | TmApp R1 M1 => fun e2 =>
                match e2 as e2' return forall R1 M1, {TmApp R1 M1 = e2'} + {TmApp R1 M1 <> e2'} with
                | TmApp R2 M2 => fun R1 M1 =>
                                  match eq_dec _ R1 R2 with
                                  | left _ => match eq_dec _ M1 M2 with
                                            | left _ => left _
                                            | right _ => right _
                                            end
                                  | right _ => right _
                                  end
                | _ => fun _ _ => right _
                end R1 M1
             | TmLam M1      => fun e2 =>
                match e2 as e2' return forall M1, {TmLam M1 = e2'} + {TmLam M1 <> e2'} with
                | TmLam M2 => fun M1 =>
                              match eq_dec _ M1 M2 with
                              | left _ => left _
                              | right _ => right _
                              end
                | _ => fun _ => right _
                end M1
             end; try congruence; try solve [intro H; invc H];
                  try solve [intro H; invc H; inv_existT; congruence].
    Defined.

    (** definitional equality by parallel reduction *)

    Inductive par_red : forall {n}, t n -> t n -> Prop :=
    | R_REFL : forall n M, @par_red n M M
    | R_BETA_OBJ : forall n M M' N N' (HM : par_red M M') (HN : par_red N N'),
        @par_red n (TmApp (TmLam M) N) (subst M' (N' :: identity_subst _)%vector)
    | R_BETA_FAM : forall n B B' N N' (HB : par_red B B') (HN : par_red N N'),
        @par_red n (TyApp (TyLam B) N) (subst B' (N' :: identity_subst _)%vector)
    | R_APP_OBJ  : forall n M M' N N' (HM : par_red M M') (HN : par_red N N'), @par_red n (TmApp M N) (TmApp M' N')
    | R_APP_FAM  : forall n A A' M M' (HA : par_red A A') (HM : par_red M M'), @par_red n (TyApp A M) (TyApp A' M')
    | R_ABS_OBJ  : forall n M M' (HM : par_red M M'), @par_red n (TmLam M) (TmLam M')
    | R_ABS_FAM  : forall n B B' (HB : par_red B B'), @par_red n (TyLam B) (TyLam B')
    | R_PI_FAM   : forall n A A' B B' (HA : par_red A A') (HB : par_red B B'), @par_red n (TyPi A B) (TyPi A' B')
    | R_PI_KIND  : forall n A A' K K' (HA : par_red A A') (HK : par_red K K'), @par_red n (KPi A K) (KPi A' K')
    .

    Inductive big_par_red : forall {n}, t n -> t n -> Prop :=
    | big_z : forall n M, @par_red n M M -> big_par_red M M
    | big_s : forall n M M' M'', @big_par_red n M M' -> big_par_red M' M'' -> big_par_red M M''
    .

    Inductive def_eq : forall {n}, t n -> t n -> Prop :=
    | def_red : forall n M1 M2, @par_red n M1 M2 -> def_eq M1 M2
    | def_symm : forall n M1 M2, def_eq M1 M2 -> @def_eq n M2 M1
    | def_trans : forall n M1 M2 M3, @def_eq n M1 M2 -> @def_eq n M2 M3 -> @def_eq n M1 M3
    .

    Module notations.
      Delimit Scope expr_scope with expr.
      Bind Scope expr_scope with expr.t.

      Coercion TmApp : expr.t >-> Funclass.
      Coercion TyApp : expr.t >-> Funclass.

      Notation "'\' e" := (expr.TmLam e) (at level 50) : expr_scope.
      Notation "'/\' e" := (expr.TyLam e) (at level 50) : expr_scope.
      Notation "A -> B" := (expr.TyPi A B) : expr_scope.

      Local Open Scope expr.

      Check (\ (TmVar Fin.F1)).
      Check ((TyConst "Nat"%string) -> (TyConst "test"%string)).

      Notation " M ~> M' " := (par_red M M') (at level 60, right associativity) : expr_scope.
      Notation " M ~>* M' " := (big_par_red M M') (at level 60, right associativity) : expr_scope.
      Notation " M == M' " := (def_eq M M') (at level 60, right associativity) : expr_scope.
    End notations.

    

    (** properties of the definitional equality wrt. parallel reduction *)

    Import notations.
    Open Scope expr.
    Check (KType ~> KType).
    Theorem diamond_property : forall n (U : t n) U' U'', U ~> U' -> U ~> U'' -> exists V, U' ~> V /\ U'' ~> V.
      (* implement Tait's method *)
    Admitted.

    Theorem church_rosser : forall n (U : t n) U' U'', (U ~>* U') -> U ~>* U'' -> exists V, U' ~>* V /\ U'' ~>* V.
    Admitted.
  End expr.


  Import LF.expr.notations.
  Open Scope expr_scope.
  Check (expr.KType == expr.KType).

  Module ctx.
    (* again, contexts are indexed by number of freevars *)
    (* later vars in the context may refer to previous bindings => by incrementing index *)
    (* ! contexts are well-formed by construction *)
    Inductive t : nat -> Type :=
    | nil : t 0
    | cons : forall n (e : expr.t n) (C : t n), t (S n)
    .

    Lemma transport : forall n m, n = m -> t n = t n.
      auto.
    Qed.

    Hint Rewrite transport.


    (* find the type of nth bound variable *)
    Fixpoint nth {n} (C : t n) : Fin.t n -> expr.t n.
      refine match C with
             | nil => fun f => _
             | cons e C => fun f => _
             end.
      - destruct f using Fin.case0.
      - apply (expr.lift 0).
        destruct f using Fin.caseS'.
        + exact e.
        + exact (nth n0 C f).
    Defined.

    Eval compute in nth (cons (expr.TmLam (expr.TmVar Fin.F1))
                          (cons (expr.KType) nil)) (Fin.FS (Fin.F1)).
    (* => expr.KType *)

    Hint Rewrite plus_n_O.
    Hint Rewrite Nat.add_succ_r.
    (* context concatenation *)
    Fixpoint concat {n} {m} (C : t n) (C' : t m) : t (n + m).
      refine match C' with
             | nil => _
             | cons e C' => _
             end.
      - replace (n + 0) with n by apply plus_n_O. exact C.
      - Search (_ + S _ = S _). replace (n + S n0) with (S (n + n0)) by (symmetry; apply Nat.add_succ_r).
        refine (cons _ _ ).
        replace (n + n0) with (n0 + n) by omega.
        exact (expr.lift_k n 0 e).
        exact (concat n n0 C C').
    Defined.

    Module test.
      Variable n : nat.
      Variable C : ctx.t n.
      Definition concat_C_nil : t n.
        replace n with (n + 0) by auto.
        exact (concat C nil).
      Defined.

      Print concat_C_nil.
    End test.
    
  End ctx.


  Module sig.
    Local Open Scope list.
    (* signature for the constant context *)
    (* invariant : each c has is constructed as `TyConst k` or `TmConst k` *)
    (* ! no need to bind free _variables_, therefore no point of indexing *)

    Definition t := list (guid.t * expr.t 0)%type.

    Inductive defined (name : guid.t) : t -> Type :=
    | Here  : forall Sig e, defined name ((name,e)::Sig)
    | There : forall Sig x e, defined name Sig -> defined name ((x,e)::Sig)
    .

    Locate "+".
    Print inl.

    Fixpoint defined_dec_ty (x : guid.t) (s : t) {struct s} : (defined x s) + (defined x s -> False).
      refine match s as s0 return (defined x s0) + (defined x s0 -> False) with
             | [] => _
             | (x',e)::s => _
             end.
      - intuition.
      - destruct (guid.eq_dec x x').
        left. rewrite e0. exact (Here x' s e).
        destruct (defined_dec_ty x s).
        left. exact (There x' e d).
        right. intuition. inv H.
        exact (n eq_refl).
        exact (f H1).
    Admitted.
    

    Fixpoint defined_dec (x : guid.t) (s : t) {struct s} : {inhabited (defined x s)} + {~ inhabited (defined x s)}.
      refine match s as s0 return {inhabited (defined x s0)} + {~ inhabited (defined x s0)} with
             | [] => _
             | (x',e)::s => _
             end.
      intuition.
      destruct (guid.eq_dec x x').
      left. rewrite e0. exact (inhabits (Here x' s e)).
      destruct (defined_dec x s).
      left. inv i. exact (inhabits (There x' e H)).
      right. intuition. inv H. inv H0.
      exact (n eq_refl).
      exact (n0 (inhabits H2)).
    Admitted.

    (**
    Fixpoint defined (x : guid.t) (s : t) : Prop :=
      match s with
      | [] => False
      | (x',e)::s => if (guid.eq_dec x x') then True else defined x s
      end. *)

    Arguments Here {_ _ _}.
    Arguments There {_ _ _ _} _.

    Definition case_nil (x : guid.t) {P : Type} (m : defined x []) : P :=
      match m with
      | Here  => I
      | There p => I
      end.

    Definition case_cons {x : guid.t} {s} (P : forall p, defined x (p :: s) -> Type)
              (PHere : forall e, P (x,e) Here)
              (PThere : forall x e m, P (x,e) (There m))
              {p} (m : defined x (p :: s)) : P p m.
    revert P PHere PThere.
    refine match m with
           | Here => _
           | There m => _
           end; auto.
    Defined.
      

    Fixpoint get (s : t) (x : guid.t) : defined x s -> expr.t 0.
      refine match s with
             | [] => fun m => case_nil m
             | (x',e)::s' => fun m => _
             end.
      destruct (x',e), m using case_cons.
      - exact e.
      - exact (get s' _ m).
    Defined.

    Definition hello_defined : defined "hello"%string [("T"%string, expr.KType) ; ("hello"%string, expr.TyConst "T"%string)] := There Here.
    Eval compute in get hello_defined.

  End sig.

  Module canonical.
    (* canonical form judgment *)
    Import expr.
    Fixpoint t {n} (e : expr.t n) {struct e} : ctx.t n -> sig.t -> Prop.
      refine match e with
             | KType => fun _ _ => True
             | KPi A K =>fun c s => _
             | TyConst k => fun c s => _
             | TyPi A B =>fun c s => _
             | TyLam B =>fun c s => False
             | TyApp A M =>fun c s => _
             | TmConst k =>fun c s => _
             | TmVar f =>fun c s => _
             | TmLam M =>fun c s => False
             | TmApp M N =>fun c s => _
             end.
      - (* KPi *) exact (t n0 A c s /\ t (S n0) K (ctx.cons A c) s).
      - (* TyConst *) destruct (sig.defined_dec_ty k s).
        refine (t _ (sig.get d) (ctx.nil) s).
        exact False.
      - (* TyPi *) exact (t n0 A c s /\ t (S n0) B (ctx.cons A c) s).
      - (* TyApp *) exact (t n0 A c s /\ t n0 M c s).
      - (* TmConst *) destruct (sig.defined_dec_ty k s).
        refine (t _ (sig.get d) ctx.nil s).
        exact False.
      - (* TmVar *) exact (t _ (ctx.nth c f) c s).
      - (* TmApp *) exact (t n0 M c s /\ t n0 N c s).
    Admitted.

    (* Fixpoint dec {n} (e : expr.t n) (c : ctx.t n) (s : sig.t) : {t e c s} + {~ t e c s}. *)


  End canonical.

  Module Judgments.
    Local Open Scope list.
    (** sig_wf    : Σ sig
        ctx_wf    : Σ >> Γ
        kind_wf   : Σ;Γ>> K
        has_kind  : Σ;Γ>> A : K
        has_type  : Σ;Γ>> M : A *)

    (** definitional equality given by equality decider
       Σ;Γ >> A ≡ A'
       Σ;Γ >> K ≡ K'
       Σ;Γ >> M ≡ M' *)

    Inductive sig_wf : sig.t -> Prop :=
    | B_EMPTY_SIG : sig_wf []
    | B_KIND_SIG  :
        forall a Sig K (Ha : sig.defined a Sig -> False) (HK : kind_wf [] ctx.nil K) (HS : sig_wf Sig), sig_wf ((a,K):: Sig)
    | B_TYPE_SIG  :
        forall c Sig A (Hc : sig.defined c Sig -> False) (HA : has_kind [] ctx.nil A expr.KType) (HS : sig_wf Sig), sig_wf ((c,A)::Sig)
    with ctx_wf : forall {n}, sig.t -> ctx.t n -> Prop :=
    | B_EMPTY_CTX : forall Sig, @ctx_wf 0 Sig ctx.nil
    | B_TYPE_CTX  : forall n Sig C A e (HC : @ctx_wf n Sig C) (HA : has_kind Sig C A expr.KType), @ctx_wf (S n) Sig (ctx.cons e C)
    with kind_wf : forall {n}, sig.t -> ctx.t n -> expr.t n -> Prop :=
    | B_TYPE_KIND : forall n Sig C (HC : ctx_wf Sig C), @kind_wf n Sig C expr.KType
    | B_PI_KIND   : forall n Sig C K A (HK : kind_wf Sig (ctx.cons A C) K), @kind_wf n Sig C (expr.KPi A K)
    with has_kind : forall {n}, sig.t -> ctx.t n -> expr.t n -> expr.t n -> Prop :=
    | B_CONST_FAM : forall Sig C c k (Hc : member.t (c,k) Sig) (HC : ctx_wf Sig C), @has_kind 0 Sig C (expr.TyConst c) k
    | B_PI_FAM    : forall n Sig C A B (HB : has_kind Sig (ctx.cons A C) B expr.KType), @has_kind n Sig C (expr.TyPi A B) expr.KType
    | B_LAM_FAM   : forall n Sig C K A B (HB : has_kind Sig (ctx.cons A C) B K), @has_kind n Sig C (expr.TyLam B) (expr.KPi A K)
    | B_CONV_FAM  : forall n Sig C A K K' (HA : has_kind Sig C A K) (HK' : kind_wf Sig C K') (Heq : K == K'),
        @has_kind n Sig C A K'
    | B_APP_FAM   : forall n Sig C A K B M (HA : has_kind Sig C A (expr.KPi B K)) (HM : has_kind Sig C M B),
        @has_kind n Sig C (expr.TyApp A M) (expr.subst K (M :: expr.identity_subst _)%vector)
    with has_type : forall {n}, sig.t -> ctx.t n -> expr.t n -> expr.t n -> Prop :=
    | B_CONST_OBJ : forall Sig C c A (HC : ctx_wf Sig  C) (Hc : member.t (c,A) Sig), @has_type 0 Sig C (expr.TmConst c) A
    | B_VAR_OBJ   : forall n Sig C (f : Fin.t n) A (HC : ctx_wf Sig C) (Hx : ctx.nth C f = A) , (has_type Sig C (@expr.TmVar n f) A)
    | B_LAM_OBJ   : forall n Sig C A B M (HM : has_type Sig (ctx.cons A C) M B), @has_type n Sig C (expr.TmLam M) (expr.TyPi A B)
    | B_APP_OBJ   : forall n Sig C A B N M (HM : has_type Sig C M (expr.TyPi A B)) (HN : has_type Sig C N A),
        @has_type n Sig C (expr.TmApp M N) (expr.subst B (N :: expr.identity_subst _)%vector)
    | B_CONV_OBJ  : forall n Sig C M A A' (HM : has_type Sig C M A) (HA' : has_kind Sig C A' expr.KType) (Heq : A == A'),
        @has_type n Sig C M A'
    .

    Hint Constructors sig_wf ctx_wf kind_wf has_kind has_type.
    (* Hint out of a module?? *)

    Module notations.
      Delimit Scope Judgments_scope with judg.
      (* Bind Scope Judgments_scope with . *)

      Notation " S >> H " := (ctx_wf S H) (at level 60).
      Notation " S ; H >> K " := (kind_wf S H K) (at level 60).
      Notation " S ; H >> A : K " := (has_kind S H A K) (at level 60).
      Notation " S ; H >> M :: A " := (has_kind S H M A) (at level 60).

    End notations.


    (** properties of the LF type theory *)
    Theorem weakening_kind : forall n m Sig (C : ctx.t n) (C' : ctx.t m) K,
        kind_wf Sig C K -> ctx_wf Sig (ctx.concat C C') -> kind_wf Sig (ctx.concat C C') (expr.lift_k m 0 K).
    Proof.
      induction C; induction C'; intros.
      (**
      inv H.

      replace (ctx.concat C ctx.nil) with C. (* computation in type !! *)
      unfold ctx.concat in *. simpl in *. simpl. *)

    Abort.

    
     
  End Judgments.
  

  Module arith.
    Locate "->".
    Local Open Scope string.
    Import expr.

    (** syntax *)
    Definition t : guid.t * expr.t 0 := ("t", KType).
    Definition z : guid.t * expr.t 0 := ("z", TyConst "t").
    Definition s : guid.t * expr.t 0 := ("s", TyPi (TyConst "t") (TyConst "t")).
    Definition plus : guid.t * expr.t 0 :=
      ("plus", (TyConst "t") -> (TyConst "t") -> (TyConst "t")).
    Definition mult : guid.t * expr.t 0 :=
      ("mult", (TyConst "t") -> (TyConst "t") -> (TyConst "t")).
     
    (** judgments *)
    (* value *)
    Definition value : guid.t * expr.t 0 := ("value", KPi (TyConst "t") KType).
    Definition v_z   : guid.t * expr.t 0 := ("v/z", TyApp (TyConst "value") (TmConst "z")).
    (* v/s : Π V : t , Π _ : value V , value (s V) *)
    Definition v_s   : guid.t * expr.t 0 :=
      ("v/s", (TyConst "t")
              -> ((TyConst "value") (TmVar Fin.F1))
              -> ((TyConst "value") ((TmConst "s") (TmVar (Fin.FS Fin.F1))))).


    (* small step judgment *)
    Definition step : guid.t * expr.t 0 := ("step", KPi (TyConst "t") (KPi (TyConst "t") KType)).
    (* step/plus/s : Π E : t, Π V : t, Π _ : value E, Π _ : value V, step (plus (s V) E) (s (plus V E)) *)
    Definition step_plus_s : guid.t * expr.t 0 :=
      ("step/plus/s", (TyConst "t") (* E *)
                      -> (TyConst "t") (* V *)
                      -> ((TyConst "value") (TmVar (Fin.FS Fin.F1))) (* value E *)
                      -> ((TyConst "value") (TmVar (Fin.FS Fin.F1))) (* value V *)
                      -> (TyConst "step")
                          ((TmConst "plus") ((TmConst "s") (TmVar (Fin.FS (Fin.FS Fin.F1)))) (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
                          ((TmConst "s") (((TmConst "plus") (TmVar (Fin.FS (Fin.FS Fin.F1)))) (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))).


    (* step/plus/z : Π V : t, Π _ : value V, step (plus z V) V *)
    Definition step_plus_z : guid.t * expr.t 0 :=
      ("step/plus/z", (TyConst "t")
                      -> (TyConst "value") (TmVar Fin.F1)
                      -> (TyConst "step") ((TyConst "plus") (TmConst "z") (TmVar (Fin.FS Fin.F1))) (TmVar (Fin.FS Fin.F1))).

    (* step/mult/s : Π E:t, Π V:t, Π _:value E, Π _:value V
                       , step (mult (s V) E) (plus (mult V E) E) *)
    Definition step_mult_s : guid.t * expr.t 0 :=
      ("step/mult/s", TyPi (TyConst "t") (* E *)
                           (TyPi (TyConst "t") (* V *)
                                 (TyPi (TyApp (TyConst "value") (TmVar (Fin.FS Fin.F1))) (* value E *)
                                       (TyPi (TyApp (TyConst "value") (TmVar (Fin.FS Fin.F1)))  (* value V *)
                                             (TyApp (TyApp (TyConst "step")
                                                           (TmApp (TmApp (TmConst "mult") (TmApp (TmConst "s") (TmVar (Fin.FS (Fin.FS Fin.F1)))))
                                                                  (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
                                                    (TmApp (TmApp (TmConst "plus") (TmApp (TmApp (TmConst "mult") (TmVar (Fin.FS (Fin.FS Fin.F1)))) (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
                                                           (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))).
    (* step/mult/z : Π V:t, Π _:value V, step (mult z V) z  *)
    Definition step_mult_z : guid.t * expr.t 0 :=
      ("step/mult/z", TyPi (TyConst "t") (* V *)
                           (TyPi (TyApp (TyConst "value") (TmVar Fin.F1))
                                 (TyApp (TyApp (TyConst "step")
                                               (TmApp (TmApp (TmConst "mult") (TmConst "z")) (TmVar (Fin.FS Fin.F1)))) (* mult z V *)
                                        (TmConst "z")))).

    (* step/congr/s : Π E:t, Π E':t, Π _:step E E', step (s E) (s E') *)
    Definition step_congr_s : guid.t * expr.t 0 :=
      ("step/congr/s", TyPi (TyConst "t") (* E:t *)
                            (TyPi (TyConst "t") (* E':t *)
                                  (TyPi (TyApp (TyApp (TyConst "step") (TmVar (Fin.FS Fin.F1))) (TmVar Fin.F1)) (* step E E' *)
                                        (TyApp (TyApp (TyConst "step") (TmApp (TmConst "s") (TmVar (Fin.FS (Fin.FS Fin.F1)))))
                                               (TmApp (TmConst "s") (TmVar (Fin.FS Fin.F1))))))).

    (* step/congr/plus1 : Π E1 E1' E2, Π _:step E1 E1', step (plus E1 E2) (plus E1' E2) *)
    Definition step_congr_plus1 : guid.t * expr.t 0 :=
      ("step/congr/plus1", TyPi (TyConst "t") (*E1*)
                                (TyPi (TyConst "t") (*E1'*)
                                      (TyPi (TyConst "t") (*E2*)
                                            (TyPi (TyApp (TyApp (TyConst "step") (TmVar (Fin.FS (Fin.FS (Fin.F1))))) (TmVar (Fin.FS Fin.F1)))
                                                  (TyApp (TyApp (TyConst "step") (TmApp (TmApp (TmConst "plus") (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (TmVar (Fin.FS Fin.F1))))
                                                         (TmApp (TmApp (TmConst "plus") (TmVar (Fin.FS (Fin.FS Fin.F1)))) (TmVar (Fin.FS Fin.F1)))))))).
                                                                  
    Definition step_congr_plus2 : guid.t * expr.t 0 :=
      ("step/congr/plus2", TyPi (TyConst "t") (*E1*)
                                (TyPi (TyConst "t") (*E2*)
                                      (TyPi (TyConst "t") (*E2'*)
                                            (TyPi (TyApp (TyApp (TyConst "step") (TmVar (Fin.FS Fin.F1))) (TmVar Fin.F1))
                                                  (TyApp (TyApp (TyConst "step")
                                                                (TmApp (TmApp (TmConst "plus") (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (TmVar (Fin.FS (Fin.FS Fin.F1)))))
                                                         (TmApp (TmApp (TmConst "plus") (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (TmVar (Fin.FS Fin.F1)))))))).
                                                    
    Definition step_congr_mult1 : guid.t * expr.t 0 :=
      ("step/congr/mult1", TyPi (TyConst "t") (*E1*)
                                (TyPi (TyConst "t") (*E1'*)
                                      (TyPi (TyConst "t") (*E2*)
                                            (TyPi (TyApp (TyApp (TyConst "step") (TmVar (Fin.FS (Fin.FS (Fin.F1))))) (TmVar (Fin.FS Fin.F1)))
                                                  (TyApp (TyApp (TyConst "step") (TmApp (TmApp (TmConst "mult") (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (TmVar (Fin.FS Fin.F1))))
                                                         (TmApp (TmApp (TmConst "plus") (TmVar (Fin.FS (Fin.FS Fin.F1)))) (TmVar (Fin.FS Fin.F1)))))))).
                                                                  
    Definition step_congr_mult2 : guid.t * expr.t 0 :=
      ("step/congr/mult2", TyPi (TyConst "t") (*E1*)
                                (TyPi (TyConst "t") (*E2*)
                                      (TyPi (TyConst "t") (*E2'*)
                                            (TyPi (TyApp (TyApp (TyConst "step") (TmVar (Fin.FS Fin.F1))) (TmVar Fin.F1))
                                                  (TyApp (TyApp (TyConst "step")
                                                                (TmApp (TmApp (TmConst "mult") (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (TmVar (Fin.FS (Fin.FS Fin.F1)))))
                                                         (TmApp (TmApp (TmConst "plus") (TmVar (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (TmVar (Fin.FS Fin.F1)))))))).

    (* big step judgment *)
    Definition big_step : guid.t * expr.t 0 :=
      ("big-step", KPi (TyConst "t") (KPi (TyConst "t") KType)).
    Definition big_step_z : guid.t * expr.t 0 :=
      ("big-step/z", TyPi (TyConst "t") (TyApp (TyApp (TyConst "big-step") (TmVar Fin.F1)) (TmVar Fin.F1))).
    Definition big_step_s : guid.t * expr.t 0 :=
      ("big-step/s", TyPi (TyConst "t") (* E1 *)
                          (TyPi (TyConst "t") (* E2 *)
                                (TyPi (TyConst "t") (* E3 *)
                                      (TyPi (TyApp (TyApp (TyConst "step") (TmVar (Fin.FS (Fin.FS Fin.F1)))) (TmVar (Fin.FS Fin.F1))) (* step E1 E2 *)
                                            (TyPi (TyApp (TyApp (TyConst "big-step") (TmVar (Fin.FS (Fin.FS Fin.F1)))) (TmVar (Fin.FS Fin.F1)))
                                                  (TyApp (TyApp (TyConst "big-step") (TmVar (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
                                                         (TmVar (Fin.FS (Fin.FS Fin.F1))))))))).

    Definition Sig : sig.t := [ t ; z ; s ; plus ; mult ; value ; v_z ; v_s
                               ; step ; step_plus_s ; step_plus_z ; step_mult_s ; step_mult_z
                               ; step_congr_plus1 ; step_congr_plus2 ; step_congr_mult1 ; step_congr_mult2
                               ; big_step ; big_step_z ; big_step_s ]%list.

  End arith.
End LF.








Module arith.
  (* arithmetic *)

  (* arith <-> arith in Coq *)

  (* indexed by number of free variables *)
  Inductive t : Type :=
  | z : t
  | s : t -> t
  | plus : t -> t -> t
  | mult : t -> t -> t
  .

  Inductive value : t -> Prop :=
  | v_z : value z
  | v_s : forall e, value e -> value (s e)
  .

  Inductive canonical : t -> Prop :=
  | c_z : canonical z
  | c_s : forall e, canonical e -> canonical (s e)
  | c_plus : forall e1 e2, canonical e1 -> canonical e2 -> canonical (plus e1 e2)
  | c_mult : forall e1 e2, canonical e1 -> canonical e2 -> canonical (mult e1 e2)
  .

  Inductive step : t -> t -> Prop :=
  | plus_step   : forall v e, value v -> step (plus (s v) e) (s (plus v e))
  | plus_z      : forall v, value v -> step (plus z v) v
  | mult_z      : forall v, value v -> step (mult z v) z
  | mult_step   : forall v e, value v -> value e -> step (mult (s v) e) (plus (mult v e) e)
  | s_congr : forall e e', step e e' -> step (s e) (s e')
  | plus_congr1 : forall e1 e1' e2, step e1 e1' -> step (plus e1 e2) (plus e1' e2)
  | plus_congr2 : forall e1 e2 e2', step e2 e2' -> step (plus e1 e2) (plus e1 e2')
  | mult_congr1 : forall e1 e1' e2, step e1 e1' -> step (mult e1 e2) (mult e1' e2)
  | mult_congr2 : forall e1 e2 e2', step e2 e2' -> step (mult e1 e2) (mult e1 e2')
  .

  Lemma value_choose : forall v, value v -> v = z \/ (exists v' , value v' /\ v = s (v')).
    induction v; intros; auto.
    right. exists v. inv H. split. assumption. reflexivity.
    inv H. inv H.
  Qed.

  Inductive big_step : nat -> t -> t -> Type :=
  | v_step : forall v, value v -> big_step 0 v v
  | s_step : forall n e e' e'', step e e' -> big_step n e' e'' -> big_step (S n) e e''
  .

  (**
  Inductive big_step : t -> t -> Prop :=
  | this : forall v, value v -> big_step v v
  | next : forall e e' e'', big_step e e' -> step e' e'' -> big_step e e''. *)

  Fixpoint to_nat (e : t) : nat :=
    match e with
    | z => 0
    | s e => S (to_nat e)
    | plus e1 e2 => (to_nat e1) + (to_nat e2)
    | mult e1 e2 => (to_nat e1) * (to_nat e2)
    end.

  Fixpoint to_t (n : nat) : t :=
    match n with
    | 0 => z
    | S n => s (to_t n)
    end.

  Hint Constructors step.
  Hint Constructors big_step.
  Hint Constructors value.
  Hint Constructors canonical.
  Hint Constructors t.

  Lemma step_to_nat_trans : forall e e', step e e' -> to_nat e = to_nat e'.
    intro e. induction e; simpl; intros; inv H; simpl in *; auto; try apply Nat.add_comm.
  Qed.

  Lemma big_step_to_nat_trans : forall n e e', big_step n e e' -> to_nat e = to_nat e'.
    intro n; induction n.
    * intros. inv H; reflexivity.
    * induction e; intros; inv H.
      + inv H1.
      + apply step_to_nat_trans in H1; rewrite H1. specialize (IHn e'0 e' H2). assumption.
      + apply step_to_nat_trans in H1; rewrite H1. specialize (IHn e'0 e' H2). assumption.
      + apply step_to_nat_trans in H1; rewrite H1. specialize (IHn e'0 e' H2). assumption.
  Qed.

  Lemma step_to_z : forall e, step e z -> to_nat e = 0.
    induction e; intros; try invc H; auto.
  Qed.

  Lemma s_step_not_z : forall e, step (s e) z -> False.
    induction e; intros; invc H.
  Qed.

  Lemma to_nat_z_false : forall e, to_nat (s e) = 0 -> False.
    intro e. induction e; simpl; intro.
    - congruence.
    - destruct (to_nat (s e)) eqn:H1. simpl in H1.
      rewrite H1 in H. congruence.
      simpl in *. inv H1. inv H.
    - inv H.
    - inv H.
  Qed.

  Lemma step_to_nat_trans_z : forall e' e, step e e' -> to_nat e' = 0 -> to_nat e = 0.
    intros. apply step_to_nat_trans in H. rewrite H; assumption.
  Qed.

  Lemma big_step_to_z : forall n e (H : big_step n e z), to_nat e = 0.
    intro n. induction n; intros.
    - inv H; simpl; reflexivity.
    - inv H. apply IHn in H2.
      apply step_to_nat_trans_z with (e' := e'); auto.
  Qed.

  Theorem adequate: forall v (Hv : value v) e n (H : big_step n e v) , to_nat v = to_nat e.
  Proof.
    intros. apply value_choose in Hv. generalize dependent e. generalize dependent n.
    destruct Hv. 
    - intros. rewrite H in *. apply big_step_to_z in H0. rewrite H0. simpl; reflexivity.
    - destruct H. intros.
      apply big_step_to_nat_trans in H0. rewrite H0; reflexivity.
  Qed.

  Fixpoint eval (e : t) : t :=
    match e with
    | z => z
    | s e => s (eval e)
    | plus e1 e2 => plus (eval e1) (eval e2)
    | mult e1 e2 => mult (eval e1) (eval e2)
    end.
End arith.


Module adequacy.

  (** LA (LF.arith) ~= CA (Coq arith) *)

  (* syntax *)
  Local Open Scope string.
  Fixpoint CL_tm_syn (e : arith.t) : LF.expr.t 0 :=
    match e with
    | arith.z => LF.expr.TmConst "z"
    | arith.s e => LF.expr.TmApp (LF.expr.TmConst "s") (CL_tm_syn e)
    | arith.plus e1 e2 => LF.expr.TmApp (LF.expr.TmApp (LF.expr.TmConst "plus") (CL_tm_syn e1)) (CL_tm_syn e2)
    | arith.mult e1 e2 => LF.expr.TmApp (LF.expr.TmApp (LF.expr.TmConst "mult") (CL_tm_syn e1)) (CL_tm_syn e2)
    end.

  Import LF.expr.
  Definition LC_tm_syn :=
    let fix outer (e : LF.expr.t 0) {struct e} : option arith.t :=
        let fix inner (t : arith.t) (e : LF.expr.t 0) {struct e} : option arith.t :=
            (case0 _ None
                (fun _ _ => None)
                (fun _ => None)
                (fun _ _ => None)
                (fun _ => None)
                (fun _ _ => None)
                (fun k => if (LF.guid.eq_dec k "s") then Some (arith.s t) else None)
                (fun _ => None)
                (fun m1 m2 =>
                   match (outer m2) with
                   | Some t' => if (LF.expr.eq_dec m1 (LF.expr.TmConst "plus"))
                               then Some (arith.plus t' t)
                               else if (LF.expr.eq_dec m1 (LF.expr.TmConst "mult"))
                                    then Some (arith.mult t' t)
                                    else None
                   | _       => None
                   end) e)
        in (case0 _
           (* PKType *)  None
           (* PKPi   *)  (fun _ _ => None)
           (* PTyConst *)  (fun _ => None)
           (* PTyPi *)  (fun _ _ => None)
           (* PTyLam *)  (fun _ => None)
           (* PTyApp *)  (fun _ _ => None)
           (* PTmConst *)  (fun k => (if (LF.guid.eq_dec k "z") then Some (arith.z) else None))
           (* PTmLam *)  (fun _ => None)
           (* PTmApp *)
           (fun m n =>
              match (outer n) with
              | Some t => inner t m
              | None   => None
              end) e)
    in outer.
  
  Module test.
    Import arith.
    Import LF.expr.
    Eval compute in LC_tm_syn (TmApp (TmConst "s") (TmApp (TmConst "s") (TmConst "z"))).
    Eval compute in LC_tm_syn (TmConst "z").
    Eval compute in LC_tm_syn (TmApp (TmApp (TmConst "plus") (TmConst "z")) (TmApp (TmConst "s") (TmConst "z"))).
    Eval compute in LC_tm_syn (CL_tm_syn (plus (plus z z) (s z))).
    Eval compute in CL_tm_syn (s (s z)).
  End test.

  Import LF.expr.
  Import LF.expr.notations.
  Import LF.Judgments.notations.
  Import LF.Judgments.
  Local Open Scope judg.
  Local Open Scope expr.
  (* Hint Constructors sig_wf ctx_wf kind_wf has_kind has_type. *)

  Theorem adequacy_syntax : forall e, arith.canonical e -> has_type LF.arith.Sig LF.ctx.nil (CL_tm_syn e) (TyConst "t").
    induction e; eauto; simpl; intros.
    - apply B_CONST_OBJ. apply B_EMPTY_CTX.
      unfold LF.arith.Sig.
      unfold LF.arith.z.
      exact (member.There member.Here).
    - assert (subst (TyConst "t") ((CL_tm_syn e) :: identity_subst 0) = TyConst "t") by auto.
      rewrite <- H0.
      apply B_APP_OBJ with (A := TyConst "t").
      apply B_CONST_OBJ. apply B_EMPTY_CTX.
      unfold LF.arith.Sig. unfold LF.arith.s.
      exact (member.There (member.There member.Here)).
      apply IHe.
      inv H; auto.
    - inv H.
      assert (subst (TyConst "t") (CL_tm_syn e2 :: identity_subst 0) = TyConst "t") by auto.
      rewrite <- H0.
      apply B_APP_OBJ with (A := TyConst "t").
      assert (subst (TyConst "t" -> TyConst "t") (CL_tm_syn e1 :: identity_subst 0) = (TyConst "t" -> TyConst "t")) by auto.
      rewrite <- H1.
      apply B_APP_OBJ with (A := TyConst "t").
      apply B_CONST_OBJ. apply B_EMPTY_CTX.
      unfold LF.arith.Sig. unfold LF.arith.plus. exact (member.There (member.There (member.There member.Here))).
      apply IHe1; auto. apply IHe2; auto.
    - inv H.
      assert (subst (TyConst "t") (CL_tm_syn e2 :: identity_subst 0) = TyConst "t") by auto.
      rewrite <- H0.
      apply B_APP_OBJ with (A := TyConst "t").
      assert (subst (TyConst "t" -> TyConst "t") (CL_tm_syn e1 :: identity_subst 0) = (TyConst "t" -> TyConst "t")) by auto.
      rewrite <- H1.
      apply B_APP_OBJ with (A := TyConst "t").
      apply B_CONST_OBJ. apply B_EMPTY_CTX.
      unfold LF.arith.Sig. unfold LF.arith.mult. exact (member.There (member.There (member.There (member.There member.Here)))).
      apply IHe1; auto. apply IHe2; auto.
  Qed.

  Theorem adequate_syntax_surjective : forall e, arith.canonical e -> LC_tm_syn (CL_tm_syn e) = Some e.
    induction e; intros.
    - simpl; reflexivity.
    - inv H. apply IHe in H1. simpl.
      rewrite H1. reflexivity.
    - inv H. apply IHe1 in H2. apply IHe2 in H3. simpl.
      rewrite H2. rewrite H3. reflexivity.
    - inv H. apply IHe1 in H2. apply IHe2 in H3. simpl.
      rewrite H2. rewrite H3. reflexivity.
  Qed.



  
  Check arith.plus_step. (* : forall v e : arith.t, arith.value v -> arith.step ... *)
  (* proof system adequacy *)
  (* a) LF type/tm -> Coq type/tm *)
  (* b) LF Arith tm -> Coq tm *)
  
  

End adequacy.





(** b) A simple theory formalized in Coq *)
(** c) The same simple theory formalized in LF *)
(** d) in Coq, prove adequacy between b) and c) *)
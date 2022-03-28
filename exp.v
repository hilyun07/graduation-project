From Coq Require Import BinNums.
From Coq Require Import Notations.
Require Import String.
Require Import Arith.
From Coq Require Import DecimalString.

Section Expression_reasoning.
Inductive exp : Set :=
| Int (z : Z)
| Var (x : string)
| Rec (x : string) (e : exp)
| Nil
| Field (e : exp) (x : string)
| Assgn (x : string) (e : exp)
| Seq (e1 : exp) (e2 : exp)
| Iet (x : string) (e1 : exp) (e2 : exp).
End Expression_reasoning.

Section Computation_law.
Definition var := string.
Variable loc : Type.
Let rec := string -> option loc.
Definition env := string -> option loc.
Definition val := (Z + rec).
Definition mem := loc -> option val.
Definition emb1 : Z -> val := fun x => inl x.
Definition emb2 : rec -> val := fun x => inr x.
Coercion emb1 : Z >-> val.
Coercion emb2 : rec >-> val.
Hypothesis loc_dec : forall l l' : loc, {l=l'} + {l<>l'}.
Definition int_of_string := NilEmpty.int_of_string.

Reserved Notation
         "s ',' m '=[' e ']=>' v ',' m'"
         (at level 40).

Inductive comp : env -> mem -> string -> val -> mem -> Prop :=
| CInt s m e n : int_of_string e = Some n -> comp s m e n m
| CVar s m x l v : Some l = s x -> Some v = m l -> comp s m (Var x) v m
| CRec s m x e l v m' : comp s m e v m' -> m l = None -> m' l = None ->  comp s m (Rec x e) (inr (fun y : string => if string_dec x y then Some l else None)) (fun y => if loc_dec l y then Some v else m' y)
| CNilRec s m : comp s m Nil (inr (fun _ => None)) m
| CField s m e v x l m' : comp s m e (inr (fun y => if string_dec x y then Some l else None)) m' -> m' l = Some v -> comp s m (Field e x) v m'
| CAssign s m e x v m' l : comp s m e v m' -> s x = Some l -> comp s m (Assgn x e) v m'
| CSeq s m1 m2 m3 e1 e2 v1 v2 : comp s m1 e1 v1 m2 -> comp s m2 e2 v2 m3 -> comp s m1 (Seq e1 e2) v2 m3
| CLet s m1 m2 m3 e1 e2 : comp s m1 e1 v1 m2 -> comp 
                                                 




Definition loc := nat.


Definition val := 

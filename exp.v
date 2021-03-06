From Coq Require Import BinNums.
From Coq Require Import Notations.
Require Import String.
Require Import Arith.
From Coq Require Import DecimalString.
Require Import List.
Import ListNotations.

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
Definition val := (Decimal.int + rec).
Definition mem := loc -> option val.
Definition emb1 : Decimal.int -> val := fun x => inl x.
Definition emb2 : rec -> val := fun x => inr x.
Coercion emb1 : Decimal.int >-> val.
Coercion emb2 : rec >-> val.
Hypothesis loc_dec : forall l l' : loc, {l=l'} + {l<>l'}.
Definition int_of_string := NilEmpty.int_of_string.

Class finmap (A B : Type) :=
  { nilmap : A -> option B;
    update_map : A -> B -> (A -> option B) -> (A -> option B);
    update_well : forall a b f, (update_map a b f) a = Some b;
    update_shadow : forall a b c f, (update_map a c (update_map a b f)) = update_map a c f;
    update_change : forall a b c d f, a <> c -> (update_map a b (update_map c d f)) = (update_map c d (update_map a b f))}.

Context `{FSL : finmap string loc}.
Context `{FLV : finmap loc val}.

Reserved Notation
         "s '/' m '=[' e ']=>' v '/' m' '*' l"
         (at level 40, m at next level, e at next level, v at next level, m' at next level, l at next level).

Inductive comp : env -> mem -> string -> val -> mem -> list loc -> Prop :=
| CInt s m e n : int_of_string e = Some n -> s/m =[e]=> n/m*nil
| CVar s m x l v : s x = Some l -> m l = Some v -> s/m =[x]=> v/m*[l]
| CRec s m x e l v m' ls : s/m =[e]=> v/m'*ls -> m l = None -> m' l = None
                        -> s/m =[("{" ++ x ++ ":=" ++ e ++ "x")%string]=>
                               (inr (update_map x l nilmap))/(update_map l v m')*(l::ls)
| CNilRec s m : s/m =["{}"]=> (inr nilmap)/m*nil
| CField s m e v x l m' ls : s/m =[e]=> (inr (update_map x l nilmap))/m'*ls -> m' l = Some v
                          -> s/m =[(e ++ "." ++ x)]=> v/m'*(l::ls)
| CAssign s m e x v m' l ls : s/m =[e]=> v/m'*ls -> s x = Some l -> s/m =[(x ++ ":=" ++ e)]=> v/(update_map l v m')*(l::ls)
| CSeq s m1 m2 m3 e1 e2 v1 v2 ls1 ls2 : s/m1 =[e1]=> v1/m2*ls1 -> s/m2 =[e2]=> v2/m3*ls2 -> s/m1 =[(e1 ++ ";" ++ e2)]=>v2/m3*(ls1++ls2)
| CLet s m1 m2 m3 e1 e2 v1 v2 l x ls1 ls2 :
  s/m1 =[e1]=> v1/m2*ls1 -> (update_map x l s)/(update_map l v1 m2) =[e2]=> v2/m3*ls2
  -> m1 l = None -> m2 l = None -> s/m1 =[("let" ++ x ++ e1 ++ e2)]=> v2/m3*(l :: ls1 ++ ls2)
where "s '/' m '=[' e ']=>' v '/' m' '*' l" := (comp s m e v m' l).
                                                
Inductive reach (s : env) (m : mem) : loc -> Prop :=
| varAc x l : s x = Some l -> reach s m l
| pntAc x l l' : reach s m l -> m l = Some (inr (update_map x l' nilmap)) -> reach s m l'.

Theorem safety s m e v m' x : forall ls l, (s/m =[e]=> v/m' * ls -> In l ls -> m l = Some x -> reach s m l).





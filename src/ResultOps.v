(**************************************************************************)
(*  This file is part of dx, a tool to derive C from monadic Gallina.     *)
(*                                                                        *)
(*  Copyright (C) 2021 Université de Lille & CNRS                         *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(**************************************************************************)

From Coq Require Import List.
From compcert.common Require Errors.

From dx Require Import ResultMonad.

Open Scope result_monad_scope.

Definition fmap {A B: Type} (f: A -> B) (x: Result A) : Result B :=
  do y <- x ;
  Ok (f y).

Definition sequence {A: Type} (xs: list (Result A)) : Result (list A) :=
  fold_right (fun y ys => do z <- y; do zs <- ys; Ok (z :: zs)) (Ok nil) xs.

Fixpoint mapM {A B: Type} (f: A -> Result B) (xs: list A) : Result (list B) :=
  match xs with
  | nil => Ok nil
  | (x :: xs') =>
    do y <- f x ;
    do ys <- mapM f xs' ;
    Ok (y :: ys)
  end.

Fixpoint foldM {A B: Type} (f: A -> B -> Result A) (x: A) (ys: list B) : Result A :=
  match ys with
  | nil => Ok x
  | (y :: ys') =>
    do z <- f x y ;
    foldM f z ys'
  end.

Fixpoint zipWithM {A B C: Type}
    (f: A -> B -> Result C) (xs: list A) (ys: list B)
    : Result (list C) :=
  match (xs, ys) with
  | ((x :: xs'), (y :: ys')) => do z  <- f x y ;
                                do zs <- zipWithM f xs' ys' ;
                                Ok (z :: zs)
  | (nil, nil)               => Ok nil
  | _                        => Err ZipMismatchedSizes
  end.

Definition combineM {A B: Type} (xs: list A) (ys: list B) : Result (list (A * B)) :=
  zipWithM (fun x y => Ok (x, y)) xs ys.

Fixpoint zipWith3M {A B C D: Type}
    (f: A -> B -> C -> Result D) (xs: list A) (ys: list B) (zs: list C)
    : Result (list D) :=
  match (xs, ys, zs) with
  | ((x :: xs'), (y :: ys'), (z :: zs')) => do u  <- f x y z ;
                                            do us <- zipWith3M f xs' ys' zs';
                                            Ok (u :: us)
  | (nil, nil, nil)                      => Ok nil
  | _                                    => Err ZipMismatchedSizes
  end.

Definition fromCompCertRes {A : Type} (x : Errors.res A) : Result A :=
  match x with
  | Errors.Error msg => Err (CompCert msg)
  | Errors.OK y => Ok y
  end.

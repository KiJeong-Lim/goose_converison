(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import github_com.goose_lang.primitive.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.github_com.goose_lang.primitive.
Require Export New.proof.proof_prelude.
Module primitive.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions primitive.pkg_name' var_addrs primitive.functions' primitive.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_UInt64Get : 
  WpFuncCall primitive.pkg_name' "UInt64Get" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_UInt32Get : 
  WpFuncCall primitive.pkg_name' "UInt32Get" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_UInt64Put : 
  WpFuncCall primitive.pkg_name' "UInt64Put" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_UInt32Put : 
  WpFuncCall primitive.pkg_name' "UInt32Put" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_RandomUint64 : 
  WpFuncCall primitive.pkg_name' "RandomUint64" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_UInt64ToString : 
  WpFuncCall primitive.pkg_name' "UInt64ToString" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Linearize : 
  WpFuncCall primitive.pkg_name' "Linearize" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Assume : 
  WpFuncCall primitive.pkg_name' "Assume" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Assert : 
  WpFuncCall primitive.pkg_name' "Assert" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Exit : 
  WpFuncCall primitive.pkg_name' "Exit" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WaitTimeout : 
  WpFuncCall primitive.pkg_name' "WaitTimeout" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_TimeNow : 
  WpFuncCall primitive.pkg_name' "TimeNow" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Sleep : 
  WpFuncCall primitive.pkg_name' "Sleep" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_NewProph : 
  WpFuncCall primitive.pkg_name' "NewProph" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_prophId'ptr_ResolveBool : 
  WpMethodCall primitive.pkg_name' "prophId'ptr" "ResolveBool" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_prophId'ptr_ResolveU64 : 
  WpMethodCall primitive.pkg_name' "prophId'ptr" "ResolveU64" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End defs.
End primitive.

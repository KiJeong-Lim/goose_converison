(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import log.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.log.
Require Export New.proof.proof_prelude.
Module log.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions log.pkg_name' var_addrs log.functions' log.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_New : 
  WpFuncCall log.pkg_name' "New" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Default : 
  WpFuncCall log.pkg_name' "Default" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_itoa : 
  WpFuncCall log.pkg_name' "itoa" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_formatHeader : 
  WpFuncCall log.pkg_name' "formatHeader" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_getBuffer : 
  WpFuncCall log.pkg_name' "getBuffer" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_putBuffer : 
  WpFuncCall log.pkg_name' "putBuffer" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_SetOutput : 
  WpFuncCall log.pkg_name' "SetOutput" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Flags : 
  WpFuncCall log.pkg_name' "Flags" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_SetFlags : 
  WpFuncCall log.pkg_name' "SetFlags" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Prefix : 
  WpFuncCall log.pkg_name' "Prefix" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_SetPrefix : 
  WpFuncCall log.pkg_name' "SetPrefix" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Writer : 
  WpFuncCall log.pkg_name' "Writer" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Print : 
  WpFuncCall log.pkg_name' "Print" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Printf : 
  WpFuncCall log.pkg_name' "Printf" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Println : 
  WpFuncCall log.pkg_name' "Println" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Fatal : 
  WpFuncCall log.pkg_name' "Fatal" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Fatalf : 
  WpFuncCall log.pkg_name' "Fatalf" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Fatalln : 
  WpFuncCall log.pkg_name' "Fatalln" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Panic : 
  WpFuncCall log.pkg_name' "Panic" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Panicf : 
  WpFuncCall log.pkg_name' "Panicf" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Panicln : 
  WpFuncCall log.pkg_name' "Panicln" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Output : 
  WpFuncCall log.pkg_name' "Output" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Fatal : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Fatal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Fatalf : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Fatalf" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Fatalln : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Fatalln" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Flags : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Flags" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Output : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Output" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Panic : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Panic" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Panicf : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Panicf" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Panicln : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Panicln" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Prefix : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Prefix" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Print : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Print" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Printf : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Printf" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Println : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Println" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_SetFlags : 
  WpMethodCall log.pkg_name' "Logger'ptr" "SetFlags" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_SetOutput : 
  WpMethodCall log.pkg_name' "Logger'ptr" "SetOutput" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_SetPrefix : 
  WpMethodCall log.pkg_name' "Logger'ptr" "SetPrefix" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_Writer : 
  WpMethodCall log.pkg_name' "Logger'ptr" "Writer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Logger'ptr_output : 
  WpMethodCall log.pkg_name' "Logger'ptr" "output" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End defs.
End log.

(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import github_com.goose_lang.primitive.disk.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.github_com.goose_lang.primitive.disk.
Require Export New.proof.disk_prelude.
Module disk.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions disk.pkg_name' var_addrs disk.functions' disk.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_Init : 
  WpFuncCall disk.pkg_name' "Init" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Get : 
  WpFuncCall disk.pkg_name' "Get" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Read : 
  WpFuncCall disk.pkg_name' "Read" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Write : 
  WpFuncCall disk.pkg_name' "Write" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Size : 
  WpFuncCall disk.pkg_name' "Size" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Barrier : 
  WpFuncCall disk.pkg_name' "Barrier" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_NewFileDisk : 
  WpFuncCall disk.pkg_name' "NewFileDisk" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_NewMemDisk : 
  WpFuncCall disk.pkg_name' "NewMemDisk" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_FileDisk_Barrier : 
  WpMethodCall disk.pkg_name' "FileDisk" "Barrier" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk_Close : 
  WpMethodCall disk.pkg_name' "FileDisk" "Close" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk_Read : 
  WpMethodCall disk.pkg_name' "FileDisk" "Read" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk_ReadTo : 
  WpMethodCall disk.pkg_name' "FileDisk" "ReadTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk_Size : 
  WpMethodCall disk.pkg_name' "FileDisk" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk_Write : 
  WpMethodCall disk.pkg_name' "FileDisk" "Write" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk'ptr_Barrier : 
  WpMethodCall disk.pkg_name' "FileDisk'ptr" "Barrier" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk'ptr_Close : 
  WpMethodCall disk.pkg_name' "FileDisk'ptr" "Close" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk'ptr_Read : 
  WpMethodCall disk.pkg_name' "FileDisk'ptr" "Read" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk'ptr_ReadTo : 
  WpMethodCall disk.pkg_name' "FileDisk'ptr" "ReadTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk'ptr_Size : 
  WpMethodCall disk.pkg_name' "FileDisk'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_FileDisk'ptr_Write : 
  WpMethodCall disk.pkg_name' "FileDisk'ptr" "Write" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk_Barrier : 
  WpMethodCall disk.pkg_name' "MemDisk" "Barrier" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk_Close : 
  WpMethodCall disk.pkg_name' "MemDisk" "Close" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk_Read : 
  WpMethodCall disk.pkg_name' "MemDisk" "Read" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk_ReadTo : 
  WpMethodCall disk.pkg_name' "MemDisk" "ReadTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk_Size : 
  WpMethodCall disk.pkg_name' "MemDisk" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk_Write : 
  WpMethodCall disk.pkg_name' "MemDisk" "Write" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk'ptr_Barrier : 
  WpMethodCall disk.pkg_name' "MemDisk'ptr" "Barrier" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk'ptr_Close : 
  WpMethodCall disk.pkg_name' "MemDisk'ptr" "Close" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk'ptr_Read : 
  WpMethodCall disk.pkg_name' "MemDisk'ptr" "Read" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk'ptr_ReadTo : 
  WpMethodCall disk.pkg_name' "MemDisk'ptr" "ReadTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk'ptr_Size : 
  WpMethodCall disk.pkg_name' "MemDisk'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MemDisk'ptr_Write : 
  WpMethodCall disk.pkg_name' "MemDisk'ptr" "Write" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End defs.
End disk.

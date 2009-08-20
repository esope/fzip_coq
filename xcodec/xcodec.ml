(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Benoît Montagu <benoit.montagu@inria.fr>                *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public License           *)
(*  version 3.0 or above.                                                 *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* The author would like to thank Nicolas Pouillard who wrote a piece     *)
(* of code from which this file is inspired.                              *)

let xcode = Char.code 'x'
let id x = x

let rec encode input =
  let n = Scanf.fscanf input "%c" Char.code in
  let () = match n with
  | n when n > 255 -> assert false
  | n when n > 128 -> Printf.printf "x%x" n
  | n when n = xcode -> Printf.printf "xx"
  | _ -> Printf.printf "%c" (Char.chr n)
  in encode input

let encode input =
  try encode input
  with End_of_file -> Printf.printf "%!"


let is_hex_digit = function
  | '0'..'9' | 'a'..'f' -> true
  | _ -> false

let string_of_four_chars c1 c2 c3 c4 =
  Printf.sprintf "%c%c%c%c" c1 c2 c3 c4

let read_hex_from_two_chars c1 c2 =
  int_of_string (string_of_four_chars '0' 'x' c1 c2)

let rec decode input =
  let c = Scanf.fscanf input "%c" id in
  let () = match Char.code c with
  | n when n = xcode ->
      let i = Scanf.fscanf input "%c" id in
      if i = 'x'
      then Printf.printf "x"
      else let j = Scanf.fscanf input "%c" id in
      if is_hex_digit i && is_hex_digit j
      then Printf.printf "%c" (Char.chr (read_hex_from_two_chars i j))
      else Printf.printf "x%c%c" i j
  | _ -> Printf.printf "%c" c
  in decode input

let decode input =
  try decode input
  with End_of_file -> Printf.printf "%!"

let exit_usage n =
  Printf.eprintf "Usage: xcodec [encode|decode]\n%!";
  exit n

let () = (* main *)
  if Array.length Sys.argv <> 2
  then exit_usage 1
  else begin
    match Sys.argv.(1) with
    | "encode" -> encode stdin
    | "decode" -> decode stdin
    | _ -> exit_usage 1
  end ;
  exit 0

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

let input = Stream.of_channel stdin

let output_stream s =
  Stream.iter (Printf.printf "%c") s; Printf.printf "%!"

let stream_of_string s =
  let n = String.length s in
  let rec aux = function
  | i when i = n -> [< >]
  | i -> [< '(s.[i]) ; aux (i+1) >] in
  aux 0

let rec encode = parser
  | [< 'c when Char.code c > 255 ; _ >] -> assert false
  | [< 'c when Char.code c > 128 ; t >] ->
      [< ''x' ; stream_of_string (Printf.sprintf "%x" (Char.code c)) ; encode t >]
  | [< ''x' ; t >] -> [< ''x' ; ''x' ; encode t >]
  | [< 'c ; t >] -> [< 'c ; encode t >]
  | [< >] -> [< >]

let is_hex_digit = function
  | '0'..'9' | 'a'..'f' -> true
  | _ -> false

let string_of_four_chars c1 c2 c3 c4 =
  Printf.sprintf "%c%c%c%c" c1 c2 c3 c4

let read_hex_from_two_chars c1 c2 =
  int_of_string (string_of_four_chars '0' 'x' c1 c2)

let rec decode = parser
  | [< 'a when a = 'x' ; 'i ; s >] ->
      if i = 'x'
      then [< ''x' ; decode s >]
      else (parser
        | [< 'j ; s >] ->
            if is_hex_digit i && is_hex_digit j
            then [< '(Char.chr (read_hex_from_two_chars i j)) ; s >]
            else [< ''x' ; 'i ; 'j ; s >]            
        | [< >] -> assert false) (decode s)
  | [< 'a ; s >] -> [< 'a ; decode s >]
  | [< >] -> [< >]

let exit_usage n =
  Printf.eprintf "Usage: xcodec [encode|decode]\n%!";
  exit n

let () = (* main *)
  if Array.length Sys.argv <> 2
  then exit_usage 1
  else begin
    match Sys.argv.(1) with
    | "encode" -> output_stream (encode input)
    | "decode" -> output_stream (decode input)
    | _ -> exit_usage 1
  end ;
  exit 0

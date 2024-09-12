open Squirrelcore
open Ppx_yojson_conv_lib.Yojson_conv.Primitives

let ( let+ ) = Result.bind

(* why are things so complicated ? *)

(** read a file of name `filestring` to a string *)
let read_file filename =
  let in_channel = open_in filename in
  let rec read_lines acc =
    try
      let line = input_line in_channel in
      read_lines (acc ^ line ^ "\n")
    with End_of_file ->
      close_in in_channel;
      acc
  in
  read_lines ""

let try_map f =
  let rec aux acc = function
    | [] -> Ok (List.rev acc)
    | hd :: tl ->
        let+ nhd = f hd in
        aux (nhd :: acc) tl
  in
  aux []

(* ----- set up ------- *)

type lts_t = LowTraceSequent.t
(** to make yojson happy *)

type cv_parameters = { num_retry : int; timeout : float } [@@deriving yojson_of]

let yojson_of_cv_parameters x = Utils.Json.to_assoc (yojson_of_cv_parameters x)
let default_parameters = { num_retry = 5; timeout = 1.0 }
let yojson_of_lts_t s = JsonExport.json_of_low_trace_sequent s

type to_cv = { parameters : cv_parameters; context : lts_t }
[@@deriving yojson_of]

let yojson_of_to_cv x = Utils.Json.to_assoc (yojson_of_to_cv x)

(* ----- return type of Cryptovampire ------ *)

type cv_return =
  | ToFile of string
  | AutoRun of string list
  | Many of cv_return list

let rec cv_return_of_yojson (s : Yojson.Safe.t) =
  match s with
  | `Assoc [ ("ToFile", `String file) ] -> Ok (ToFile file)
  | `Assoc [ ("AutoRun", `List l) ] ->
      let+ l =
        try_map (function `String s -> Ok s | _ -> Error "not a string") l
      in
      Ok (AutoRun l)
  | `Assoc [ ("Many", `List x) ] ->
      let+ inner = try_map cv_return_of_yojson x in
      Ok (Many inner)
  | _ -> Error "not an assoc"

let result_of_yojson f_ok f_err = function
  | `Assoc [ ("Ok", t) ] ->
      let+ o = f_ok t in
      Ok (Ok o)
  | `Assoc [ ("Err", e) ] ->
      let+ e = f_err e in
      Ok (Error e)
  | _ -> Error "wrong JSON format"

let rec string_of_cv_return = function
  | ToFile file ->
      Printf.sprintf "wrote to the smt file to the file/directory \"%s\"" file
  | AutoRun runs ->
      let run_lines =
        List.mapi (fun i s -> Printf.sprintf "%dth run: \"%s\"" (i + 1) s) runs
      in
      Printf.sprintf "ran automatically:\n%s" (String.concat "\n\t- " run_lines)
  | Many returns ->
      let many_lines =
        List.mapi
          (fun i r -> Printf.sprintf "#%d:\n%s" (i + 1) (string_of_cv_return r))
          returns
      in
      Printf.sprintf "ran many times:\n---------\n%s\n---------"
        (String.concat "\n" many_lines)

let parse_result_cv_return_from_json json_str =
  try
    (* Parse the JSON string into a Yojson.Basic.t *)
    let json = Yojson.Safe.from_string json_str in
    let str_json s = Ok (string_of_yojson s) in
    let+ r = result_of_yojson cv_return_of_yojson str_json json in
    r
  with
  | Yojson.Json_error msg ->
      Printf.printf "here";
      Error (Printf.sprintf "JSON parsing error: %s\n" msg)
  | _ -> Error (Printf.sprintf "Unexpected error during JSON parsing\n")
(* ----- logic of the tactic ------- *)

(**
  try to run cryptovampire

  I dumps everything to json to be read by cryptovampire

  I couldn't figure out a sane way to execute a command give it an stdin and
  read both its stdout, stderr and return code once it terminates. I could even
  figure out how to launch a program and get its stdout and return code!

  So instead I'm doing the very terrible thing of building a sanitize oneliner
  shell script where I pipe everything the right way. I get that shell script's
  return code, then I re-read the output that I'm intersted in.
 *)
let run_cryptovampire (parameters : cv_parameters) (s : LowTraceSequent.t) =
  let json = yojson_of_to_cv { context = s; parameters } in
  let { num_retry; timeout } = parameters in

  (* TODOS:
     - [-] the cryptovampire side (mostly there)
     - [x] actually call cv from squirrel and deal with its output
     - [ ] parametrize things (be it cv itself, or the interface between cv and squirrel )
  *)

  (* --- get info from the environement --- *)

  (* cryptovampire executable location, default to looking in the path*)
  let cryptovampire_exe =
    Option.value
      (Sys.getenv_opt "CRYPTOVAMPIRE_EXECUTABLE")
      ~default:"cryptovampire"
  in
  let json_file_name, json_oc =
    match Sys.getenv_opt "SQUIRREL_CRYPTOVAMPIRE_JSON_LOCATION" with
    | Some f -> (f, open_out_gen [ Open_creat; Open_trunc; Open_wronly ] 0o777 f)
    | None -> Filename.open_temp_file "cryptovampire-stdin" ".json"
  in
  let pretty =
    Option.is_some (Sys.getenv_opt "SQUIRREL_CRYPTOVAMPIRE_JSON_PRETTY")
  in

  (* prepare to gather what cv outputs *)
  let stdout_name, stdout_file =
    Filename.open_temp_file "cryptovampire-stdout" ".json"
  in
  let stderr_name, stderr_file =
    Filename.open_temp_file "cryptovampire-stderr" ".txt"
  in

  let content =
    if pretty then Yojson.Safe.pretty_to_string json
    else Yojson.Safe.to_string json
  in

  (* print to file *)
  let ppf = Format.formatter_of_out_channel json_oc in
  Format.fprintf ppf "%s@." content;
  Format.printf "\njson exported to %s\n" json_file_name;

  (* close all files *)
  close_out json_oc;
  close_out stdout_file;
  close_out stderr_file;

  let cv_args =
    [
      "--input-format";
      "squirrel-json";
      "--output-format";
      "json";
      (* "-pn"; *)
      "auto";
      "--num-of-retry";
      string_of_int num_retry;
      "--timeout";
      string_of_float timeout;
    ]
  in
  (* this is kinda like a shell script that runs vampire *)
  let cmd =
    Filename.quote_command cryptovampire_exe ~stdin:json_file_name
      ~stdout:stdout_name ~stderr:stderr_name cv_args
  in

  Format.printf "running the command \"%s\"\n" cmd;

  let status = Unix.system cmd in
  let+ code =
    match status with
    | Unix.WEXITED code -> Ok code
    | _ ->
        Error
          "cryptovampire was killed, or otherwise stopped by some external \
           factor"
  in
  if code <> 0 then Error (read_file stderr_name)
  else
    let result_str = read_file stdout_name in
    let result = parse_result_cv_return_from_json result_str in
    let+ result =
      Result.map_error
        (function s -> Printf.sprintf "%s\n\t --> %s" s result_str)
        result
    in
    Format.printf "CryptoVampire succeded:\n%s\n" (string_of_cv_return result);
    Ok ()

module L = Location
module TA = TacticsArgs

(** parse the arguments for the `cryptovampire` tactic *)
let parse_args =
  let aux acc = function
    (* ~nt=[x] for num of retry *)
    | TA.NList ({ L.pl_desc = "nt" }, [ { L.pl_desc = nt } ]) -> (
        match int_of_string_opt nt with
        | Some nt -> { acc with num_retry = nt }
        | None ->
            Tactics.(
              hard_failure (Failure (Printf.sprintf "%s in not a number" nt))))
    (* ~t=[x] for timeout *)
    | TA.NList ({ L.pl_desc = "t" }, [ { L.pl_desc = nt } ]) -> (
        match float_of_string_opt nt with
        | Some nt -> { acc with timeout = nt }
        | None ->
            Tactics.(
              hard_failure (Failure (Printf.sprintf "%s in not a number" nt))))
    | _ -> Tactics.(hard_failure (Failure "unrecognized argument"))
  in
  List.fold_left aux default_parameters

(* register the tactic *)
let () =
  let pq_sound =
    Option.is_some (Sys.getenv_opt "SQUIRREL_CRYPTOVAMPIRE_FORCE_QUANTUM")
  in

  ProverTactics.register_general "cryptovampire" ~pq_sound
    (* ^^^^^^^^^^^^ don't know if cv is post-quantum safe, so I'll assume it's not *)
    (fun args s sk fk ->
      let args =
        match args with
        | [ Named_args args ] -> args
        | [] -> []
        | _ -> assert false
      in
      let s =
        match s with
        | Goal.Global _ ->
            Tactics.(
              hard_failure
                (Failure "CryptoVampire doesn't support global goals"))
        | Goal.Local s -> s
      in
      let parameters = parse_args args in
      match run_cryptovampire parameters s with
      | Ok () -> sk [] fk
      | Error e -> fk (None, Tactics.Failure e))

(* benchmarks, stolen for the `smt` tactic *)
let () =
  let benchmarks =
    match Sys.getenv_opt "CRYPTOVAMPIRE_BENCHMARKS" with
    | None -> []
    | Some s -> String.split_on_char ':' s
  in
  let run s =
    match run_cryptovampire default_parameters s with
    | Ok _ ->
        Format.eprintf "crypotvampire success";
        true
    | Error e ->
        Format.eprintf "crypotvampire %s" e;
        false
  in
  let bench_name = "crypotvampire" in
  if List.mem "constr" benchmarks then
    TraceSequent.register_query_alternative bench_name (fun ~precise:_ s q ->
        let s =
          match q with
          | None -> s
          | Some q ->
              let conclusion = Term.mk_ands (List.map Term.Lit.lit_to_form q) in
              TraceSequent.set_conclusion conclusion s
        in
        run s);
  if List.mem "autosimpl" benchmarks then
    TraceTactics.AutoSimplBenchmark.register_alternative bench_name (fun s ->
        (run s, None));
  TraceTactics.AutoSimplBenchmark.register_alternative "AutoSimpl" (fun s ->
      match
        TraceTactics.simpl_direct ~red_param:Reduction.rp_default ~strong:true
          ~close:true s
      with
      | Ok [] -> (true, None)
      | Error _ -> (false, None)
      | Ok _ -> assert false);
  if List.mem "auto" benchmarks then
    TraceTactics.AutoBenchmark.register_alternative bench_name (fun (_, s) ->
        run s)

(** {2. Entry kind} *)

module Entry = struct
  type kind = ModuleType | Module | Functor | Type | Value
  type t = { entry_kind : kind; entry_name : string; entry_documented : bool }

  let entry_is_documented { entry_documented; _ } = entry_documented

  let pp_kind fmt kind =
    let open Format in
    match kind with
    | ModuleType -> pp_print_string fmt "ModuleType"
    | Module -> pp_print_string fmt "Module"
    | Functor -> pp_print_string fmt "Functor"
    | Type -> pp_print_string fmt "Type"
    | Value -> pp_print_string fmt "Value"

  let pp fmt { entry_kind; entry_name; entry_documented } =
    Format.fprintf fmt "{ kind : %a; name : %s; documented : %b }" pp_kind
      entry_kind entry_name entry_documented
end

let is_documented comments loc =
  Merlin_analysis.Ocamldoc.associate_comment comments loc Location.none
  |> fst |> Option.is_some

(** {2. Look for entries in the typed tree and tries to associate comments} *)

module Implementation = struct
  open Typedtree
  open Entry

  (** [pattern_idents ns loc path] returns the list of fresh identifiers
    introduced by [vb] *)
  let rec pattern_idents : type k. k general_pattern -> string list =
   fun pat ->
    match pat.pat_desc with
    | Tpat_var (id, _) -> [ Ident.name id ]
    | Tpat_alias (pat, id, _) -> Ident.name id :: pattern_idents pat
    | Tpat_array pats | Tpat_construct (_, _, pats, _) | Tpat_tuple pats ->
        List.concat_map pattern_idents pats
    | Tpat_variant (_, Some pat, _) | Tpat_lazy pat | Tpat_exception pat ->
        pattern_idents pat
    | Tpat_record (fields, _) ->
        List.concat_map (fun (_, _, pat) -> pattern_idents pat) fields
    | Tpat_or (pat1, pat2, _) ->
        List.append (pattern_idents pat1) (pattern_idents pat2)
    | _ -> []

  let fully_qualified_name ns ident =
    String.concat "." @@ List.rev (Ident.name ident :: ns)

  let entries_of_value_binding ns comments binding =
    let entry_documented = is_documented comments binding.vb_loc in
    List.map
      (fun ident ->
        {
          entry_name = String.concat "." @@ List.rev (ident :: ns);
          entry_kind = Value;
          entry_documented;
        })
      (pattern_idents binding.vb_pat)

  let entries_of_type_declaration ns comments decl =
    [
      {
        entry_name = fully_qualified_name ns decl.typ_id;
        entry_kind = Type;
        entry_documented = is_documented comments decl.typ_loc;
      };
    ]

  let rec entries_of_module_binding ns comments binding =
    Option.fold binding.mb_id ~none:[] ~some:(fun ident ->
        {
          entry_name = fully_qualified_name ns ident;
          entry_kind =
            (match binding.mb_expr.mod_desc with
            | Tmod_functor (_, _) -> Functor
            | _ -> Module);
          entry_documented = is_documented comments binding.mb_loc;
        }
        :: entries_of_module_expr ns comments ident binding.mb_expr)

  and entries_of_module_expr ns comments ident expr =
    match expr.mod_desc with
    | Tmod_structure structure ->
        List.concat_map
          (entries_of_struct_item (Ident.name ident :: ns) comments)
          structure.str_items
    | Tmod_functor (_, expr) -> entries_of_module_expr ns comments ident expr
    | _ -> []

  and entries_of_struct_item ns comments str_item : Entry.t list =
    match str_item.str_desc with
    | Tstr_value (_, bindings) ->
        List.concat_map (entries_of_value_binding ns comments) bindings
    | Tstr_type (_, decls) ->
        List.concat_map (entries_of_type_declaration ns comments) decls
    | Tstr_module binding -> entries_of_module_binding ns comments binding
    | Tstr_recmodule bindings ->
        List.concat_map (entries_of_module_binding ns comments) bindings
    | _ -> []

  let to_entries ns comments s =
    List.concat_map (entries_of_struct_item ns comments) s.str_items
end

(** {2. Read comments } *)

let make_config path =
  let mconfig = Mconfig.initial in
  let path = Merlin_utils.Misc.canonicalize_filename path in
  let filename = Filename.basename path in
  let directory = Filename.dirname path in
  let mconfig =
    {
      mconfig with
      query = { mconfig.query with verbosity = 1; filename; directory };
    }
  in
  Mconfig.get_external_config path mconfig

let merlin_source target =
  let file_channel = open_in target in
  let file_size = in_channel_length file_channel in
  let file_content = really_input_string file_channel file_size in
  close_in file_channel;
  Msource.make file_content

let toplevel_entry comments name =
  Entry.
    {
      entry_kind = Module;
      entry_name = name;
      entry_documented = is_documented comments Location.none;
    }

let to_entries target =
  let mconfig = make_config target in
  let msource = merlin_source target in

  let unit = Mconfig.unitname mconfig in

  let pipeline = Mpipeline.make mconfig msource in

  Mpipeline.with_pipeline pipeline (fun _ ->
      let typing = Mpipeline.typer_result pipeline in
      let typedtree = Mtyper.get_typedtree typing in
      let comments = Mpipeline.reader_comments pipeline in
      toplevel_entry comments unit
      ::
      (match typedtree with
      | `Implementation s -> Implementation.to_entries [ unit ] comments s
      | _ -> assert false))

let () =
  let entries = to_entries "example.ml" in
  let fmt = Format.std_formatter in
  Format.pp_print_list Entry.pp fmt entries

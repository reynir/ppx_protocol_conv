module Default_parameters = Ppx_protocol_driver.Default_parameters
module Make = Json.Make

(** Test parameters. *)
module Test = struct
  module Standard = struct
    module Json = Make(Default_parameters)
    type u = A | B of int
    and t = {
      int: int;
      u: u;
      uu: u;
    } [@@deriving protocol ~driver:(module Json)]
    let t = { int = 5; u = A; uu = B 5 }
  end

  module Field_upper = struct
    module Json = Make(
      struct
        include Default_parameters
        let field_name name = "F_" ^ name
        let variant_name name = "V_" ^ name
      end)
    type u = A | B of int
    and t = {
      int: int;
      u: u;
      uu: u;
      v: [ `A of int ]
    } [@@deriving protocol ~driver:(module Json)]

    let t = { int = 5; u = A; uu = B 5; v = `A 6 }
  end

  module Singleton_as_list = struct
    module Json = Make(
      struct
        include Default_parameters
        let constructors_without_arguments_as_string = false
      end)
    type u = A | B of int
    and t = {
      int: int;
      u: u;
      uu: u;
      v: [ `X | `Y of int ];
    } [@@deriving protocol ~driver:(module Json)]

    let t = { int = 5; u = A; uu = B 5; v = `X }
  end

  module Omit_default = struct
    module Json = Make(
      struct
        include Default_parameters
        let omit_default_values = true
      end)
    type u = A | B of int
    and t = {
      int: int; [@default 5]
      u: u;
      uu: u;
    } [@@deriving protocol ~driver:(module Json)]

    let t = { int = 5; u = A; uu = B 5 }
  end

  module Keep_default = struct
    module Json = Make(
      struct
        include Default_parameters
        let omit_default_values = false
      end)

    type u = A | B of int
    and t = {
      int: int; [@default 5]
      u: u;
      uu: u;
    } [@@deriving protocol ~driver:(module Json)]

    let t = { int = 5; u = A; uu = B 5 }
  end

  module Field_name_count = struct
    let count = ref 0
    module Json = Make(
      struct
        include Default_parameters
        let field_name name = incr count; name
      end)
    type u = A of { x:int; y: int; z:int } | B
    [@@deriving protocol ~driver:(module Json)]
    type t = {
      a: int;
      b: int;
      c: u;
    }
    [@@deriving protocol ~driver:(module Json)]
    let expect = !count
    let t = { a=5; b=5; c=B }

  end

  module Variant_name_count = struct
    let count = ref 0
    module Json = Make(
      struct
        include Default_parameters
        let variant_name name = incr count; name
      end)
    type t = A of u | B
    and u = X of t | Y
    [@@deriving protocol ~driver:(module Json)]
    let expect = !count
    let t = A (X (A (X ( B))))
  end

  module Test_lazy = struct
    module Json = Make(
      struct
        include Default_parameters
        let eager = false
      end)
    type t = int * int lazy_t
    [@@deriving protocol ~driver:(module Json)]

  end

  module Yojson_test = struct
    module Json = Json.Yojson
    type 'a v = A of int | B of { int: int; t: 'a } | C [@name "C-D"]
    and t = {
      int : int [@default 5];
      float: float [@key "Float"];
      string: string;
      t_option: t option;
      int_option: int option;
      int_list: int list;
      v: t v;
      u: [`A of int | `B of t | `C [@name "CC"] ]
    }
    [@@deriving protocol ~driver:(module Json)]

    let tree =
      { int = 5;
        float = 6.0;
        string = "TestStr";
        t_option = None;
        int_option = Some 7;
        int_list = [4;5;6;7;8];
        v = C;
        u = `A 5;
      }
    let tree =
      { tree with
        v = B { int = 100; t = tree};
        u = `C;
      }
    let tree =
      { tree with
        v = A 21;
        u = `B tree;
        int = 7;
      }
      let yojson_result =  {|
        {
          "int": 7,
          "Float": 6.0,
          "string": "TestStr",
          "t_option": null,
          "int_option": 7,
          "int_list": [ 4, 5, 6, 7, 8 ],
          "v": [ "A", 21 ],
          "u": [
            "B",
            {
              "Float": 6.0,
              "string": "TestStr",
              "t_option": null,
              "int_option": 7,
              "int_list": [ 4, 5, 6, 7, 8 ],
              "v": [
                "B",
                {
                  "int": 100,
                  "t": {
                    "Float": 6.0,
                    "string": "TestStr",
                    "t_option": null,
                    "int_option": 7,
                    "int_list": [ 4, 5, 6, 7, 8 ],
                    "v": [ "C-D" ],
                    "u": [ "A", 5 ]
                  }
                }
              ],
              "u": [ "CC" ]
            }
          ]
        } |} |> Yojson.Safe.from_string

    let t = tree
  end

end

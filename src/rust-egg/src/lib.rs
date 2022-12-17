use ocaml_interop::{
    ocaml_export, OCaml, OCamlInt, OCamlRef, 
};

ocaml_export! {
    fn rust_twice(cr, num: OCamlRef<OCamlInt>) -> OCaml<OCamlInt> {
        let num: i64 = num.to_rust(cr);
        unsafe { OCaml::of_i64_unchecked(num * 2) }
    }
}

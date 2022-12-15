use ocaml_interop::{
    ocaml_export, FromOCaml, OCamlInt, OCaml, OCamlBytes,
    OCamlRef, ToOCaml,
};

// `ocaml_export` expands the function definitions by adding `pub` visibility and
// the required `#[no_mangle]` and `extern` declarations. It also takes care of
// acquiring the OCaml runtime handle and binding it to the name provided as
// the first parameter of the function.
ocaml_export! {
    // The first parameter is a name to which the GC frame handle will be bound to.
    // The remaining parameters must have type `OCamlRef<T>`, and the return
    // value `OCaml<T>`.
    fn rust_twice(cr, num: OCamlRef<OCamlInt>) -> OCaml<OCamlInt> {
        let num: i64 = num.to_rust(cr);
        unsafe { OCaml::of_i64_unchecked(num * 2) }
    }

    fn rust_increment_bytes(
        cr,
        bytes: OCamlRef<OCamlBytes>,
        first_n: OCamlRef<OCamlInt>,
    ) -> OCaml<OCamlBytes> {
        let first_n: i64 = first_n.to_rust(cr);
        let first_n = first_n as usize;
        let mut vec: Vec<u8> = bytes.to_rust(cr);

        for i in 0..first_n {
            vec[i] += 1;
        }

        vec.to_ocaml(cr)
    }
}
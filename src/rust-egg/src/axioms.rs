use std::fs::File;
use std::path::Path;
use std::io::{Read, Write, Result};

use crate::{
    goal_preprocess::*,
};
use serde::{Serialize, Deserialize};
use std::collections::LinkedList;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct Axioms(pub LinkedList<GoalSExpr>);

pub fn load_axioms<P: AsRef<Path>>(path: P) -> Axioms {
    if let Ok(mut file) = File::open(path) {
        let mut buf = vec![];
        if file.read_to_end(&mut buf).is_ok() {
            if let Ok(contents) = serde_json::from_slice(&buf[..]) {
                return contents;
            }
        }
    }
    
    Axioms(LinkedList::new())
}

pub fn save_axioms<P: AsRef<Path>>(path: P, axioms: Axioms) -> Result<()> {
    let mut f = File::create(path)?;
    let buf = serde_json::to_vec(&axioms)?;
    f.write_all(&buf[..])?;
    Ok(())
}
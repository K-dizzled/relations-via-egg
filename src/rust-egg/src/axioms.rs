use std::fs::File;
use std::path::Path;
use std::io::{Read, Write, Result};
use egg::*;

use crate::{
    goal_preprocess::*,
    RelRules,
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

fn rewrite_in_runtime(name: &str, from: &str, to: &str) -> Rewrite<RelLanguage, ()> {
    let searcher: Pattern<RelLanguage> = from.parse::<Pattern<RelLanguage>>().unwrap();
    let core_applier: Pattern<RelLanguage> = to.parse::<Pattern<RelLanguage>>().unwrap();

    Rewrite::new(name.to_string(), searcher, core_applier).unwrap()
}

pub fn extract_rules_from_axioms(axioms: &Axioms) -> Result<RelRules> {
    let mut rules = vec![];
    for (ind, axiom) in axioms.0.iter().enumerate() {
        if let GoalSExpr::Application(f, args) = axiom {
            if args.len() != 2 {
                continue;
            }

            let expr1 = expr_to_rellang(args.front().unwrap())
                .unwrap()
                .to_string();

            let expr2 = expr_to_rellang(args.back().unwrap())
                .unwrap()
                .to_string();

            match f.as_str() {
                "@inclusion" => {
                    rules.push( rewrite_in_runtime(
                        &format!("Wf_{}", ind),
                        expr1.as_str(),
                        expr2.as_str()
                    ));
                },
                "@same_relation" => {
                    rules.push( rewrite_in_runtime(
                        &format!("Wf_{}", ind),
                        expr1.as_str(),
                        expr2.as_str()
                    ));
                    rules.push( rewrite_in_runtime(
                        &format!("Wf_{}_rev", ind),
                        expr2.as_str(),
                        expr1.as_str()
                    ));
                },
                _ => return Err(std::io::Error::new(std::io::ErrorKind::Other, "Unknown axiom")),
            }
        }
    }

    Ok(rules)
}

pub fn extend_rules_w_axioms(wf: &mut RelRules) -> Result<()> {
    let axioms = load_axioms("axioms.json");
    let axioms_rules = extract_rules_from_axioms(&axioms)?;
    wf.extend(axioms_rules);
    Ok(())
}


// Never gonna give you up
// Never gonna let you down
// Never gonna run around and desert you
// Never gonna make you cry
// Never gonna say goodbye
// Never gonna tell a lie and hurt you
use annotate_snippets::display_list::DisplayList;
use indexmap::{IndexMap, IndexSet};
use metamath_knife::database::DbOptions;
use metamath_knife::formula::{NodeId, Tree};
use metamath_knife::nameck::{Atom, NameReader, Nameset};
use metamath_knife::proof::{ProofTreeArray, ProofTreePrinter};
use metamath_knife::scopeck::{Hyp, ScopeResult};
use metamath_knife::statement::StatementAddress;
use metamath_knife::verify::ProofBuilder as _;
use metamath_knife::{Database, StatementRef, StatementType};
use std::collections::{hash_map, BTreeMap, HashMap};
use std::fs::File;
use std::io::{self, BufWriter, Read, Write};
use std::process::Command;

#[derive(Debug)]
pub struct Importer<'a> {
    /// The input source text (as a byte slice)
    source: &'a [u8],
    /// The position in the input
    idx: usize,
    cnums: &'a [&'a str],
    vnums: &'a [&'a str],
}

#[derive(Clone, PartialEq, Eq)]
enum SExpr<'a> {
    Var(&'a str),
    App(&'a str, Vec<SExpr<'a>>),
}

impl<'a> std::fmt::Debug for SExpr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(s) => write!(f, "{s}"),
            Self::App(s, args) => {
                write!(f, "({s}")?;
                for arg in args {
                    write!(f, " {arg:?}")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Formula<'a> {
    hyps: Vec<SExpr<'a>>,
    concl: Option<(usize, SExpr<'a>)>,
}

impl<'a> Formula<'a> {
    fn literal(&self, i: usize) -> (Option<usize>, &SExpr<'a>) {
        match self.concl {
            Some((n, ref concl)) => match i.cmp(&n) {
                std::cmp::Ordering::Less => (Some(i), &self.hyps[i]),
                std::cmp::Ordering::Equal => (None, concl),
                std::cmp::Ordering::Greater => (Some(i - 1), &self.hyps[i - 1]),
            },
            None => (Some(i), &self.hyps[i]),
        }
    }
}

#[derive(Debug)]
struct MMFormula<'a> {
    vars: Vec<&'a str>,
    subst: HashMap<&'a str, SExpr<'a>>,
    hyps: Vec<SExpr<'a>>,
    concl: SExpr<'a>,
}

#[derive(Debug)]
enum InputFmla<'a> {
    Axiom(&'a str, MMFormula<'a>),
    Hyp(usize, SExpr<'a>),
}

#[derive(Debug)]
struct Input<'a> {
    inputs: Vec<InputFmla<'a>>,
    conjecture: SExpr<'a>,
    vars: Vec<&'a str>,
}

impl<'a> SExpr<'a> {
    fn subst(&mut self, subst: &mut HashMap<&'a str, SExpr<'a>>, vnums: Option<&[&'a str]>) {
        match self {
            SExpr::Var(v) => {
                if let Some(v) = v.strip_prefix('X') {
                    if let Some(e) = subst.get(v) {
                        *self = e.clone()
                    } else if let Some(vnums) = vnums {
                        let n = subst.len();
                        subst.insert(v, SExpr::Var(vnums[n]));
                        *self = SExpr::Var(vnums[n]);
                    }
                } else {
                    *self = SExpr::App(v, vec![])
                }
            }
            SExpr::App(_, args) => {
                for arg in args {
                    arg.subst(subst, vnums)
                }
            }
        }
    }

    fn push_literal(self, pos: bool, f: &mut Formula<'a>) {
        match self {
            SExpr::App("not", args) => {
                let [a]: [_; 1] = args.try_into().unwrap();
                a.push_literal(!pos, f)
            }
            SExpr::App("p", args) => {
                let [a]: [_; 1] = args.try_into().unwrap();
                if pos {
                    assert!(f.concl.replace((f.hyps.len(), a)).is_none());
                } else {
                    f.hyps.push(a);
                }
            }
            k => panic!("unknown literal kind {k:?}"),
        }
    }

    fn into_formula(mut self) -> Formula<'a> {
        let mut f = Formula {
            hyps: vec![],
            concl: None,
        };
        loop {
            match self {
                SExpr::Var("false") => break,
                SExpr::App("or", args) => {
                    let [a, b]: [_; 2] = args.try_into().unwrap();
                    a.push_literal(true, &mut f);
                    self = b;
                }
                _ => {
                    self.push_literal(true, &mut f);
                    break;
                }
            }
        }
        f
    }

    fn into_mmformula(mut self, ax: bool, cnums: &[&'a str], vnums: &[&'a str]) -> MMFormula<'a> {
        let mut vars = vec![];
        let mut subst = HashMap::new();
        let mut hyps = vec![];
        loop {
            match self {
                SExpr::App("!", args2) => {
                    let [SExpr::Var(v), b]: [_; 2] = args2.try_into().unwrap() else { panic!() };
                    let v = v
                        .strip_prefix('X')
                        .expect("forall variable not starting with X");
                    if !ax {
                        subst.insert(v, SExpr::App(cnums[vars.len()], vec![]));
                    }
                    vars.push(v);
                    self = b;
                }
                SExpr::App("=>", args2) => {
                    let [SExpr::App("p", arg), b]: [_; 2] = args2.try_into().unwrap() else { panic!() };
                    let [mut a]: [_; 1] = arg.try_into().unwrap();
                    a.subst(&mut subst, if ax { Some(vnums) } else { None });
                    hyps.push(a);
                    self = b;
                }
                SExpr::App("p", arg) => {
                    let [mut concl]: [_; 1] = arg.try_into().unwrap();
                    concl.subst(&mut subst, if ax { Some(vnums) } else { None });
                    if !vars.iter().all(|x| subst.contains_key(x)) {
                        dbg!(&vars, &subst);
                    }
                    return MMFormula {
                        vars,
                        subst,
                        hyps,
                        concl,
                    };
                }
                _ => panic!(),
            }
        }
    }
}

#[derive(Debug)]
enum StepKind<'a> {
    Input,
    Instantiate(&'a str, Vec<(&'a str, SExpr<'a>)>),
    Resolve(&'a str, usize, &'a str, usize),
    Propositional(&'a str),
}

enum Proof<'a> {
    Axiom(&'a str, &'a MMFormula<'a>, Vec<Proof<'a>>),
    InputHyp(usize, &'a SExpr<'a>),
    Conjecture(Box<Proof<'a>>),
    Hyp(usize),
    App(&'a str, Vec<Proof<'a>>),
    Instantiate(&'a str, Vec<(&'a str, SExpr<'a>)>),
}

impl<'a> std::fmt::Debug for Proof<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Axiom(s, _, _) => write!(f, "(axiom {s})"),
            Self::InputHyp(n, _) => write!(f, "h{n:?}"),
            Self::Conjecture(p) => write!(f, "(conjecture {p:?})"),
            Self::Hyp(n) => write!(f, "h{n:?}"),
            Self::App(s, args) => {
                write!(f, "({s}")?;
                for arg in args {
                    write!(f, " {arg:?}")?;
                }
                write!(f, ")")
            }
            Self::Instantiate(step, inst) => write!(f, "{step}{inst:?}"),
        }
    }
}

#[derive(Debug)]
struct Step<'a> {
    fmla: Formula<'a>,
    proof: Proof<'a>,
}

impl<'a> Importer<'a> {
    fn cur(&self) -> u8 {
        self.source[self.idx]
    }
    fn cur_opt(&self) -> Option<u8> {
        self.source.get(self.idx).copied()
    }

    fn ws(&mut self) {
        while self.idx < self.source.len() {
            let c = self.cur();
            if c.is_ascii_whitespace() {
                self.idx += 1;
                continue;
            }
            if c == b';' && self.source.get(self.idx + 1) == Some(&b';') {
                self.idx += 1;
                while self.idx < self.source.len() {
                    let c = self.cur();
                    self.idx += 1;
                    if c == b'\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn ident_opt(&mut self) -> Option<&'a str> {
        let (start, end);
        if self.cur_opt() == Some(b'"') {
            self.idx += 1;
            start = self.idx;
            while self.cur() != b'"' {
                self.idx += 1
            }
            end = self.idx;
            self.idx += 1;
            self.ws();
        } else {
            start = self.idx;
            while self.idx < self.source.len() {
                let c = self.cur();
                if c.is_ascii_whitespace() || c == b'(' || c == b')' {
                    break;
                }
                self.idx += 1;
            }
            if self.idx == start {
                return None;
            }
            end = self.idx;
        }
        self.ws();
        Some(std::str::from_utf8(&self.source[start..end]).unwrap())
    }

    fn ident(&mut self) -> &'a str {
        self.ident_opt()
            .unwrap_or_else(|| panic!("at {}: expecting identifier", self.idx))
    }

    fn chr_opt(&mut self, c: u8) -> Option<usize> {
        if self.cur_opt()? != c {
            return None;
        }
        self.idx += 1;
        (Some(self.idx), self.ws()).0
    }

    fn chr(&mut self, c: u8) -> usize {
        self.chr_opt(c)
            .unwrap_or_else(|| panic!("expecting '{}'", c as char))
    }

    fn open_opt(&mut self) -> Option<usize> {
        self.chr_opt(b'(')
    }
    fn close_opt(&mut self) -> Option<usize> {
        self.chr_opt(b')').map(|n| n + 1)
    }
    fn open(&mut self) -> usize {
        self.chr(b'(')
    }
    fn close(&mut self) -> usize {
        self.chr(b')') + 1
    }

    fn sexpr(&mut self) -> SExpr<'a> {
        if self.open_opt().is_some() {
            let head = self.ident();
            let mut args = vec![];
            loop {
                if self.close_opt().is_some() {
                    return SExpr::App(head, args);
                }
                args.push(self.sexpr())
            }
        }
        SExpr::Var(self.ident())
    }

    fn path(&mut self) -> usize {
        let mut depth = 0;
        self.open();
        loop {
            if self.close_opt().is_some() {
                return depth;
            }
            match self.ident() {
                "1" => {
                    self.close();
                    return depth;
                }
                "2" => depth += 1,
                _ => panic!("invalid path"),
            }
        }
    }

    fn read_input(&mut self) -> Input<'a> {
        self.ws();
        let mut inputs = vec![];
        let mut conjecture = None;
        while self.open_opt().is_some() {
            let ax = match self.ident() {
                "axiom" => true,
                "conjecture" => false,
                _ => panic!(),
            };
            let name = self.ident();
            let fmla = self.sexpr().into_mmformula(ax, self.cnums, self.vnums);
            self.close();
            if ax {
                inputs.push(InputFmla::Axiom(name, fmla))
            } else {
                assert!(conjecture.is_none());
                conjecture = Some(fmla);
            }
        }
        let fmla = conjecture.unwrap();
        for (n, hyp) in fmla.hyps.into_iter().enumerate() {
            inputs.push(InputFmla::Hyp(n, hyp));
        }
        Input {
            inputs,
            conjecture: fmla.concl,
            vars: fmla.vars,
        }
    }

    fn read_ivy(
        &mut self,
        input: &Input<'a>,
        db: &'a Database,
        unmangle: &'a HashMap<String, &'a [u8]>,
        label: &'a str,
    ) -> Result<String, String> {
        self.ws();
        self.open();
        let mut inputs = input.inputs.iter();
        let mut steps = HashMap::<&str, Step>::new();
        let proof = loop {
            self.open();
            let step = self.ident();
            self.open();
            let just = match self.ident() {
                "input" => StepKind::Input,
                "instantiate" => {
                    let step = self.ident();
                    self.open();
                    let mut inst = vec![];
                    while self.open_opt().is_some() {
                        let v = self.ident();
                        self.chr(b'.');
                        inst.push((v, self.sexpr()));
                        self.close();
                    }
                    self.close();
                    StepKind::Instantiate(step, inst)
                }
                "resolve" => {
                    StepKind::Resolve(self.ident(), self.path(), self.ident(), self.path())
                }
                "propositional" => StepKind::Propositional(self.ident()),
                k => panic!("unknown step kind {k}"),
            };
            self.close();
            let fmla = self.sexpr().into_formula();
            assert_eq!(self.ident(), "NIL");
            self.close();
            let proof = match just {
                StepKind::Input => {
                    if fmla.concl.is_none() {
                        if fmla.hyps.is_empty() {
                            let Some(InputFmla::Hyp(i, e)) = inputs.find(
                                |hyp| matches!(hyp, InputFmla::Hyp(_, e) if *e == input.conjecture),
                            ) else { panic!() };
                            Proof::Conjecture(Box::new(Proof::InputHyp(*i, e)))
                        } else {
                            assert!(fmla.hyps.len() == 1 && fmla.hyps[0] == input.conjecture);
                            Proof::Conjecture(Box::new(Proof::Hyp(0)))
                        }
                    } else {
                        'a: loop {
                            break match inputs.next().unwrap() {
                                InputFmla::Axiom(th, f) => {
                                    let mut subproof = vec![];
                                    for v in &f.hyps {
                                        let Some(i) = fmla.hyps.iter().position(|p| v == p)
                                        else { continue 'a };
                                        subproof.push(Proof::Hyp(i))
                                    }
                                    Proof::Axiom(th, f, subproof)
                                }
                                InputFmla::Hyp(i, e) => Proof::InputHyp(*i, e),
                            };
                        }
                    }
                }
                StepKind::Propositional(name) => {
                    let step2 = steps.get(name).unwrap();
                    match (&fmla.concl, &step2.fmla.concl) {
                        (None, None) => {}
                        (Some((_, concl)), Some((_, concl2))) => assert!(concl == concl2),
                        _ => panic!(),
                    }
                    let subproof = (step2.fmla.hyps.iter())
                        .map(|v| Proof::Hyp(fmla.hyps.iter().position(|p| v == p).unwrap()))
                        .collect();
                    Proof::App(name, subproof)
                }
                StepKind::Resolve(name1, path1, name2, path2) => {
                    let step1 = steps.get(name1).unwrap();
                    let step2 = steps.get(name2).unwrap();
                    let lit1 = step1.fmla.literal(path1);
                    let lit2 = step2.fmla.literal(path2);
                    let l1 = step1.fmla.hyps.len();
                    let l2 = step2.fmla.hyps.len();
                    assert!(lit1.1 == lit2.1);
                    match (lit1.0, lit2.0) {
                        (None, Some(i)) => Proof::App(
                            name2,
                            (l1..l1 + i)
                                .map(Proof::Hyp)
                                .chain([Proof::App(name1, (0..l1).map(Proof::Hyp).collect())])
                                .chain((l1 + i..l1 + l2 - 1).map(Proof::Hyp))
                                .collect(),
                        ),
                        (Some(i), None) => Proof::App(
                            name1,
                            (0..i)
                                .map(Proof::Hyp)
                                .chain([Proof::App(
                                    name2,
                                    (l1 - 1..l1 + l2 - 1).map(Proof::Hyp).collect(),
                                )])
                                .chain((i..l1 - 1).map(Proof::Hyp))
                                .collect(),
                        ),
                        _ => panic!(),
                    }
                }
                StepKind::Instantiate(name, inst) => Proof::Instantiate(name, inst),
            };
            if fmla.hyps.is_empty() && fmla.concl.is_none() {
                break proof;
            } else {
                assert!(steps.insert(step, Step { fmla, proof }).is_none());
            }
        };
        self.close();
        if self.idx != self.source.len() {
            panic!("expected '(' or EOF")
        }
        let max = steps.len() * 100;
        let mut builder = ProofBuilder::new(db, self.cnums, &input.vars, unmangle, label, max)?;
        let inst = builder.inst(Default::default());
        let ProofStep::Thm(n) = builder.expand(&steps, &proof, &[], inst)? else { panic!() };
        builder.arr.qed = n;
        let pr = ProofTreePrinter::new(
            db,
            builder.label,
            metamath_knife::proof::ProofStyle::Compressed,
            &builder.arr,
        );
        Ok(format!("{pr}"))
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
struct VarId(u32);
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
struct ExprId(u32);
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
struct InstId(u32);

#[derive(Clone, Hash, PartialEq, Eq)]
enum Expr<'a> {
    Var(&'a str),
    App(StatementAddress, Box<[ExprId]>),
}

#[derive(Copy, Clone)]
enum ProofStep {
    Step(ProofId, ExprId),
    Thm(ProofId),
}

impl ProofStep {
    fn id(&self) -> ProofId {
        match *self {
            ProofStep::Step(n, _) => n,
            ProofStep::Thm(_) => panic!(),
        }
    }
}

type ProofId = usize;

struct ProofBuilder<'a> {
    db: &'a Database,
    ns: &'a Nameset,
    scope: &'a ScopeResult,
    unmangle: &'a HashMap<String, &'a [u8]>,
    label: &'a [u8],
    arr: ProofTreeArray,
    hyps: Vec<StatementAddress>,
    vars: HashMap<String, StatementAddress>,
    exprs: IndexMap<Expr<'a>, ProofId>,
    insts: IndexSet<BTreeMap<&'a str, ExprId>>,
    cache: HashMap<(&'a str, InstId), ProofStep>,
    by_expr: HashMap<ExprId, ProofId>,
    csubst: HashMap<&'a str, &'a str>,
    limit: usize,
}

fn identch1(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}
fn identch(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn is_ident(v: &[u8]) -> bool {
    match v {
        [] | [b'_'] => false,
        [c, s @ ..] => identch1(*c) && s.iter().all(|&c| identch(c)),
    }
}

fn mangle(v: &[u8]) -> String {
    match v {
        [] => "null".to_owned(),
        [c, s @ ..] if identch1(*c) => {
            let mut out = vec![*c];
            out.extend(s.iter().map(|&c| if identch(c) { c } else { b'_' }));
            String::from_utf8(out).unwrap()
        }
        _ => String::from_utf8(
            b"_".iter()
                .copied()
                .chain(v.iter().map(|&c| if identch(c) { c } else { b'_' }))
                .collect(),
        )
        .unwrap(),
    }
}

fn mangle_var<'a>(v: &'a [u8], db: &'a Database, addr: StatementAddress) -> String {
    match v {
        b"A" => "A2".to_owned(),
        b"B" => "B2".to_owned(),
        b"x" => "x3".to_owned(),
        b"y" => "y1".to_owned(),
        _ if is_ident(v) => std::str::from_utf8(v).unwrap().to_owned(),
        _ => mangle(db.statement_by_address(addr).label()),
    }
}

impl<'a> ProofBuilder<'a> {
    fn new(
        db: &'a Database,
        cnums: &'a [&'a str],
        vars2: &'a [&'a str],
        unmangle: &'a HashMap<String, &'a [u8]>,
        label: &'a str,
        limit: usize,
    ) -> Result<Self, String> {
        let mut hyps = vec![];
        let mut vars = HashMap::new();
        let scope = db.scope_result();
        let ns = db.name_result();
        let label = unmangle.get(label).cloned().unwrap_or(label.as_bytes());
        let frame = scope.get(label).ok_or_else(|| {
            format!(
                "couldn't find {} in set.mm",
                std::str::from_utf8(label).unwrap()
            )
        })?;
        for hyp in &*frame.hypotheses {
            match *hyp {
                Hyp::Essential(addr, _) => hyps.push(addr),
                Hyp::Floating(addr, i, _) => {
                    let v = mangle_var(ns.atom_name(frame.var_list[i]), db, addr);
                    vars.insert(v, addr);
                }
            }
        }
        Ok(Self {
            db,
            ns,
            scope,
            unmangle,
            arr: ProofTreeArray::new(false),
            hyps,
            vars,
            label,
            exprs: Default::default(),
            insts: Default::default(),
            cache: Default::default(),
            by_expr: Default::default(),
            csubst: cnums.iter().copied().zip(vars2.iter().copied()).collect(),
            limit,
        })
    }

    fn expr(&mut self, parent: Option<(StatementAddress, usize)>, expr: Expr<'a>) -> ExprId {
        let n;
        match self.exprs.entry(expr) {
            indexmap::map::Entry::Occupied(e) => n = e.index(),
            indexmap::map::Entry::Vacant(e) => {
                n = e.index();
                match *e.key() {
                    Expr::Var(v) => {
                        let addr = if let Some(addr) = self.vars.get(v) {
                            *addr
                        } else {
                            let tc = match parent {
                                Some((addr, i)) => {
                                    let frame = self
                                        .scope
                                        .get(self.db.statement_by_address(addr).label())
                                        .unwrap();
                                    let Hyp::Floating(addr, ..) = frame.hypotheses[i] else { panic!() };
                                    self.db.statement_by_address(addr).math_at(0).slice
                                }
                                None => b"wff",
                            };
                            let var: &[_] = match tc {
                                b"wff" => b"wph",
                                b"setvar" => b"vx", // FIXME: use a fresh variable for DV avoidance
                                b"class" => b"cA",
                                _ => panic!("unknown typecode"),
                            };
                            let addr = self.ns.lookup_label(var).unwrap().address;
                            self.vars.insert(v.to_owned(), addr);
                            addr
                        };
                        e.insert(self.arr.build(addr, vec![], &[], 0..0));
                    }
                    Expr::App(addr, ref args) => {
                        let args = args.clone();
                        let hyps = args.iter().map(|&i| self.exprs[i.0 as usize]).collect();
                        let value = self.arr.build(addr, hyps, &[], 0..0);
                        self.exprs.insert(Expr::App(addr, args), value);
                    }
                }
            }
        };
        ExprId(n as u32)
    }

    fn inst(&mut self, inst: BTreeMap<&'a str, ExprId>) -> InstId {
        InstId(self.insts.insert_full(inst).0 as u32)
    }

    fn step(
        &mut self,
        steps: &HashMap<&'a str, Step<'a>>,
        step: &'a str,
        args: &[ProofStep],
        inst: InstId,
    ) -> Result<ProofStep, String> {
        if let Some(&n) = self.cache.get(&(step, inst)) {
            return Ok(n);
        }
        assert!(steps[step].fmla.hyps.len() == args.len());
        let n = self.expand(steps, &steps[step].proof, args, inst)?;
        self.cache.insert((step, inst), n);
        self.limit -= 1;
        if self.limit == 0 {
            return Err("step limit exceeded".into());
        }
        Ok(n)
    }

    fn var(&mut self, parent: Option<(StatementAddress, usize)>, v: &'a str) -> ExprId {
        self.expr(parent, Expr::Var(v))
    }

    fn sexpr(
        &mut self,
        parent: Option<(StatementAddress, usize)>,
        e: &SExpr<'a>,
        inst: InstId,
    ) -> Result<ExprId, String> {
        Ok(match e {
            &SExpr::Var(v) => self.insts[inst.0 as usize]
                .get(v)
                .copied()
                .unwrap_or_else(|| self.var(parent, v)),
            SExpr::App(t, args) => match self.csubst.get(t) {
                Some(v) if args.is_empty() => self.var(parent, v),
                _ => {
                    let t = t
                        .strip_prefix('c')
                        .ok_or_else(|| format!("unsupported term {t}"))?;
                    let t = self.unmangle.get(t).cloned().unwrap_or(t.as_bytes());
                    let t = self
                        .ns
                        .lookup_label(t)
                        .unwrap_or_else(|| {
                            panic!(
                                "missing term constructor {}",
                                std::str::from_utf8(t).unwrap()
                            )
                        })
                        .address;
                    let args = args
                        .iter()
                        .enumerate()
                        .map(|(i, e)| self.sexpr(Some((t, i)), e, inst))
                        .collect::<Result<_, _>>()?;
                    self.expr(parent, Expr::App(t, args))
                }
            },
        })
    }

    fn compose_inst(
        &mut self,
        inst1: &[(&'a str, SExpr<'a>)],
        inst2: InstId,
    ) -> Result<InstId, String> {
        let mut inst = BTreeMap::default();
        for &(v, ref e) in inst1 {
            inst.insert(v, self.sexpr(None, e, inst2)?);
        }
        for (&v, &e) in &self.insts[inst2.0 as usize] {
            if !inst.contains_key(v) {
                inst.insert(v, e);
            }
        }
        Ok(self.inst(inst))
    }

    fn expand(
        &mut self,
        steps: &HashMap<&'a str, Step<'a>>,
        proof: &Proof<'a>,
        args: &[ProofStep],
        inst: InstId,
    ) -> Result<ProofStep, String> {
        Ok(match *proof {
            Proof::Axiom(th, fmla, ref args2) => {
                let ret = self.sexpr(None, &fmla.concl, inst)?;
                if let Some(&n) = self.by_expr.get(&ret) {
                    return Ok(ProofStep::Step(n, ret));
                }
                let mut it = args2.iter();
                let th = self.unmangle.get(th).cloned().unwrap_or(th.as_bytes());
                let frame = self.scope.get(th).ok_or_else(|| {
                    let th = std::str::from_utf8(th).unwrap();
                    if th.contains("_b") {
                        return format!("missing theorem {th}, bundled theorems are unsupported");
                    }
                    panic!("missing theorem {th}")
                })?;
                let args = frame
                    .hypotheses
                    .iter()
                    .map(|hyp| {
                        Ok(match *hyp {
                            Hyp::Essential(..) => {
                                let proof = it.next().unwrap_or_else(|| {
                                    let th = std::str::from_utf8(th).unwrap();
                                    panic!("theorem {th} has more than {} arguments", args2.len())
                                });
                                self.expand(steps, proof, args, inst)?.id()
                            }
                            Hyp::Floating(addr, i, _) => {
                                let v =
                                    mangle_var(self.ns.atom_name(frame.var_list[i]), self.db, addr);
                                let n = self.sexpr(
                                    None,
                                    fmla.subst.get(&*v).ok_or_else(|| {
                                        format!(
                      "substitution to variable {v} not found in {}, probably because of lambda",
                      std::str::from_utf8(th).unwrap()
                    )
                                    })?,
                                    inst,
                                )?;
                                self.exprs[n.0 as usize]
                            }
                        })
                    })
                    .collect::<Result<_, String>>()?;
                if it.next().is_some() {
                    let th = std::str::from_utf8(th).unwrap();
                    panic!("theorem {th} has fewer than {} arguments", args2.len())
                }
                let th = self.ns.lookup_label(th).unwrap().address;
                let n = self.arr.build(th, args, &[], 0..0);
                self.by_expr.insert(ret, n);
                ProofStep::Step(n, ret)
            }
            Proof::InputHyp(i, e) => {
                let ret = self.sexpr(None, e, inst)?;
                if let Some(&n) = self.by_expr.get(&ret) {
                    return Ok(ProofStep::Step(n, ret));
                }
                let n = self.arr.build(self.hyps[i], vec![], &[], 0..0);
                self.by_expr.insert(ret, n);
                ProofStep::Step(n, ret)
            }
            Proof::Conjecture(ref p) => ProofStep::Thm(self.expand(steps, p, args, inst)?.id()),
            Proof::Hyp(i) => args[i],
            Proof::App(step, ref args2) => {
                let args2 = args2
                    .iter()
                    .map(|p| self.expand(steps, p, args, inst))
                    .collect::<Result<Vec<_>, _>>()?;
                self.step(steps, step, &args2, inst)?
            }
            Proof::Instantiate(step, ref inst2) => {
                let inst3 = self.compose_inst(inst2, inst)?;
                self.step(steps, step, args, inst3)?
            }
        })
    }

    fn print_expr(&self, n: ExprId, w: &mut impl io::Write) -> io::Result<()> {
        match *self.exprs.get_index(n.0 as usize).unwrap().0 {
            Expr::Var(n) => write!(w, "{n}"),
            Expr::App(t, ref args) => {
                write!(
                    w,
                    "({:?}",
                    std::str::from_utf8(self.db.statement_by_address(t).label()).unwrap()
                )?;
                for &e in &**args {
                    write!(w, " ")?;
                    self.print_expr(e, w)?;
                }
                write!(w, ")")
            }
        }
    }

    #[allow(unused)]
    fn print_inst(&self, n: InstId, w: &mut impl io::Write) -> io::Result<()> {
        write!(w, "(")?;
        let mut first = true;
        for (&s, &e) in &self.insts[n.0 as usize] {
            if !std::mem::take(&mut first) {
                write!(w, " ")?
            }
            write!(w, "{s}=")?;
            self.print_expr(e, w)?
        }
        write!(w, ")")
    }

    #[allow(unused)]
    fn print_subst(&self, subst: &[ExprId], w: &mut impl io::Write) -> io::Result<()> {
        write!(w, "(")?;
        let mut first = true;
        for &e in subst {
            if !std::mem::take(&mut first) {
                write!(w, " ")?
            }
            self.print_expr(e, w)?
        }
        write!(w, ")")
    }
}

#[allow(unused)]
struct MMProofPrinter<'a> {
    db: &'a Database,
    steps: Vec<Option<u32>>,
    cur: u32,
}

impl<'a> MMProofPrinter<'a> {
    #[allow(unused)]
    fn write_line(
        &self,
        pb: &ProofBuilder<'_>,
        s: String,
        expr: ExprId,
        indent: usize,
        w: &mut impl io::Write,
    ) -> io::Result<()> {
        if s.len() <= indent {
            write!(w, "{s:indent$} |- ")?;
        } else {
            write!(w, "{s}\n{:indent$} |- ", "")?;
        }
        pb.print_expr(expr, w)?;
        writeln!(w)?;
        Ok(())
    }
}

fn write_lisp_stub(
    db: &Database,
    stmt: &StatementRef<'_>,
    uses: bool,
    name: &str,
    w: &mut impl std::io::Write,
    nreader: &mut NameReader<'_>,
) {
    fn rec_write(w: &mut impl std::io::Write, db: &Database, tree: &Tree<Atom>, i: NodeId) {
        let stmt = db.statement_by_label(tree[i]).unwrap_or_else(|| {
            panic!(
                "missing: {:?}",
                std::str::from_utf8(db.name_result().atom_name(tree[i])).unwrap()
            )
        });
        if stmt.statement_type() == StatementType::Floating {
            write!(w, "{:?}", mangle_var(&stmt.math_at(1), db, stmt.address())).unwrap();
        } else {
            write!(w, "({:?}", mangle(stmt.label())).unwrap();
            for i in tree.children_iter(i) {
                write!(w, " ").unwrap();
                rec_write(w, db, tree, i)
            }
            write!(w, ")").unwrap();
        }
    }

    let nset = &**db.name_result();
    let grammar = &**db.grammar_result();
    let frame = db.scope_result().get(stmt.label()).unwrap_or_else(|| {
        panic!(
            "theorem not found: {}",
            std::str::from_utf8(stmt.label()).unwrap()
        )
    });
    match grammar.parse_statement(stmt, nset, nreader) {
        Ok(Some(f)) => {
            write!(w, "(theorem {name:?} (for").unwrap();
            let mut ess = vec![];
            for hyp in &*frame.hypotheses {
                match *hyp {
                    Hyp::Essential(addr, _) => ess.push(addr),
                    Hyp::Floating(addr, i, tc) => write!(
                        w,
                        " ({:?} ({:?}))",
                        mangle_var(nset.atom_name(frame.var_list[i]), db, addr),
                        mangle(nset.atom_name(tc))
                    )
                    .unwrap(),
                }
            }
            write!(w, ") (for").unwrap();
            for addr in ess {
                let hyp = db.statement_by_address(addr);
                let f = grammar
                    .parse_statement(&hyp, nset, nreader)
                    .unwrap()
                    .unwrap();
                write!(w, " ({:?} ", mangle(hyp.label())).unwrap();
                rec_write(w, db, &f.tree, f.root);
                write!(w, ")").unwrap();
            }
            write!(w, ") (for) ").unwrap();
            rec_write(w, db, &f.tree, f.root);
            if uses && stmt.statement_type() == StatementType::Provable {
                write!(w, "\n  (uses").unwrap();
                for (_, used) in stmt.use_iter() {
                    if used != b"?" {
                        write!(w, " {:?}", mangle(used)).unwrap();
                    }
                }
                writeln!(w, "))").unwrap();
            } else {
                writeln!(w, " nil)").unwrap();
            }
        }
        Ok(None) => {
            write!(w, "(term {name:?} (").unwrap();
            for hyp in &*frame.hypotheses {
                match *hyp {
                    Hyp::Essential(..) => panic!("essential hyp in syntax axiom {name}"),
                    Hyp::Floating(_, _, tc) => {
                        write!(w, " ({:?})", mangle(nset.atom_name(tc))).unwrap()
                    }
                }
            }
            writeln!(w, " ({:?})))", mangle(&stmt.math_at(0))).unwrap();
        }
        Err(e) => {
            db.render_diags(vec![(stmt.address(), e.into())], |snippet| {
                eprintln!("{}", DisplayList::from(snippet))
            });
            std::process::exit(1)
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let mut db = Database::new(DbOptions {
        incremental: true,
        ..Default::default()
    });
    let setmm = args.next().unwrap();
    let mut tgt = args.next();
    if tgt.as_deref() == Some("+") {
        let mut extra = format!("$[ {setmm} $]\n").into_bytes();
        File::open(args.next().unwrap())
            .unwrap()
            .read_to_end(&mut extra)
            .unwrap();
        db.parse("extra".to_owned(), vec![("extra".to_owned(), extra)]);
        tgt = Some(args.next().unwrap());
    } else {
        db.parse(setmm, vec![]);
    }
    db.name_pass();
    db.grammar_pass();

    let mut unmangle = HashMap::new();
    for stmt in db.statements() {
        if stmt.is_assertion() {
            let s = mangle(stmt.label());
            match unmangle.entry(s) {
                hash_map::Entry::Occupied(e) => {
                    let s = e.key().clone();
                    for i in 1.. {
                        if let hash_map::Entry::Vacant(e) = unmangle.entry(format!("{s}{i}")) {
                            e.insert(stmt.label());
                            break;
                        }
                    }
                }
                hash_map::Entry::Vacant(e) => {
                    e.insert(stmt.label());
                }
            }
        }
    }
    let mut nreader = NameReader::new(db.name_result());
    if let Some(tgt) = tgt {
        let tgt_stmt = db.statement(tgt.as_bytes()).expect("theorem not found");
        let tgt = mangle(tgt.as_bytes());
        eprintln!("{tgt}");
        std::env::set_current_dir("..").unwrap();
        write_lisp_stub(
            &db,
            &tgt_stmt,
            true,
            &tgt,
            &mut BufWriter::new(File::create(format!("tmp/a{tgt}_thm.mm0")).unwrap()),
            &mut nreader,
        );
        let stat = Command::new("bin/hammer.sh")
            .arg(format!("a{tgt}_thm"))
            .status()
            .unwrap();
        if !stat.success() {
            std::process::exit(stat.code().unwrap_or(1))
        }
        let cnums = &*(1..100)
            .map(|i| &*Box::leak(format!("c{i}").into_boxed_str()))
            .collect::<Vec<_>>();
        let vnums = &*(0..100)
            .map(|i| &*Box::leak(format!("v{i}").into_boxed_str()))
            .collect::<Vec<_>>();
        let results = std::thread::scope(|s| {
            let mut results = vec![];
            let (db, tgt, unmangle) = (&db, &tgt, &unmangle);
            for i in [960, 480, 240, 120, 80, 40] {
                let jh = std::thread::Builder::new()
                    .name(format!("prem{i}"))
                    .spawn_scoped(s, move || {
                        let stat = Command::new("bin/runprob1.sh")
                            .args([15.to_string(), format!("tmp/a{tgt}_thm.p.prem{i}")])
                            .output()
                            .unwrap();
                        assert!(stat.status.success(), "runprob1 killed");
                        let result =
                            match std::fs::read(format!("tmp/a{tgt}_thm.p.prem{i}.small.lisp")) {
                                Ok(file2) => {
                                    let input = Importer {
                                        source: &file2,
                                        idx: 0,
                                        cnums,
                                        vnums,
                                    }
                                    .read_input();
                                    let file =
                                        std::fs::read(format!("tmp/a{tgt}_thm.p.prem{i}.ivy"))
                                            .unwrap();
                                    Importer {
                                        source: &file,
                                        idx: 0,
                                        cnums,
                                        vnums,
                                    }
                                    .read_ivy(&input, db, unmangle, tgt)
                                }
                                Err(e) if matches!(e.kind(), std::io::ErrorKind::NotFound) => {
                                    Err("prover failed".to_owned())
                                }
                                Err(e) => Err(e.to_string()),
                            };
                        (format!("prem{i}"), stat, result)
                    });
                results.push(jh.unwrap());
            }
            results
                .into_iter()
                .map(|jh| jh.join().unwrap())
                .collect::<Vec<_>>()
        });
        if let Some(s) = results
            .iter()
            .filter_map(|p| p.2.as_ref().ok())
            .min_by_key(|s| s.len())
        {
            println!("{s}")
        } else {
            eprintln!("all reconstruction attempts failed.");
            for (name, stat, result) in results {
                eprintln!("\n{name}: result = {result:?}");
                std::io::stderr().write_all(&stat.stderr).unwrap();
                std::io::stdout().write_all(&stat.stdout).unwrap();
                std::io::stdout().flush().unwrap();
            }
            std::process::exit(1);
        }
    } else {
        let mut w = std::io::stdout().lock();
        for stmt in db.statements() {
            if stmt.is_assertion() {
                write_lisp_stub(
                    &db,
                    &stmt,
                    true,
                    &mangle(stmt.label()),
                    &mut w,
                    &mut nreader,
                );
            }
        }
    }
}

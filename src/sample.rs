#![allow(non_snake_case, unused_variables)]

use std::collections::VecDeque;
use std::io::{self, BufWriter, Write};
use std::str::FromStr;

struct Scanner {
  stdin: io::Stdin,
  tokens: VecDeque<String>,
}

impl Scanner {
  fn new() -> Scanner {
    Scanner { stdin: io::stdin(), tokens: VecDeque::new() }
  }

  fn next<T: FromStr>(&mut self) -> T {
    loop {
      if let Some(tok) = self.tokens.pop_front() {
        match tok.parse() {
          Ok(v) => return v,
          Err(_) => panic!("cannot parse token: {}", tok),
        }
      }
      let mut line = String::new();
      if self.stdin.read_line(&mut line).expect("read error") == 0 {
        panic!("unexpected end of input");
      }
      self.tokens.extend(line.split_whitespace().map(String::from));
    }
  }
}

fn main() {
  let mut sc = Scanner::new();
  let stdout = io::stdout();
  let mut out = BufWriter::new(stdout.lock());

  let N: usize = sc.next();
  let M: i32 = sc.next();
  let B: usize = sc.next();
  let edges: usize = sc.next();

  let mut matches = vec![[0i32; 2]; edges];
  for i in 0..edges {
    matches[i][0] = sc.next();
    matches[i][1] = sc.next();
  }

  let W = 2 * N - 1;
  let mut grid = vec![vec![0i32; W]; W];

  for r in 0..W {
    for c in 0..W {
      grid[r][c] = sc.next();
    }
  }

  let mut bonus = vec![vec![false; W]; W];
  for _ in 0..B {
    let r: usize = sc.next();
    let c: usize = sc.next();
    bonus[r][c] = true;
  }

  let mut seed: i32 = 42;
  let moves = 20;

  writeln!(out, "{}", moves).unwrap();

  let mut i = 0;
  while i < moves {
    seed = (seed * 8009 + 104729) % (1 << 16);
    let num = seed as usize % (W * W);
    let r = num / W;
    let c = num % W;

    if grid[r][c] == -1 {
      continue;
    }

    let dir = if num % 2 == 0 { 1 } else { -1 };

    writeln!(out, "{} {} {}", r, c, dir).unwrap();
    i += 1;
  }

  out.flush().unwrap();
}

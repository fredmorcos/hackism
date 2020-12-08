// use crate::inst::Dest;
use crate::inst::Inst;
use crate::inst::Label;
// use crate::inst::{Comp, Label};
use crate::loc::Loc;
use crate::loc::SrcLoc;
use crate::srcloc;

pub struct Lex<'b> {
  buf: &'b [u8],
  index: usize,
  loc: Loc,
}

impl<'b> Lex<'b> {
  pub fn new(buf: &'b [u8]) -> Self {
    Self { buf, index: usize::default(), loc: Loc::default() }
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ErrKind {
  CommentEOF,
  CommentByte(u8),
  AddrEOF,
  AddrNumByte(u8),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Err {
  srcloc: SrcLoc,
  loc: Loc,
  kind: ErrKind,
}

impl Err {
  pub fn new(srcloc: SrcLoc, loc: Loc, kind: ErrKind) -> Self {
    Self { srcloc, loc, kind }
  }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Tok<'b>(Loc, Inst<'b>);

impl<'b> Iterator for Lex<'b> {
  type Item = Result<Tok<'b>, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    macro_rules! next {
      ($on_eof:block) => {
        if let Some(&c) = self.buf.get(0) {
          self.buf = &self.buf[1..];
          self.loc.inc(c);
          c
        } else $on_eof
      };
    }

    let mut c = next!({ return None });

    'LOOP: loop {
      if c.is_ascii_whitespace() {
        loop {
          c = next!({ return None });

          if !c.is_ascii_whitespace() {
            continue 'LOOP;
          }
        }
      } else if c == b'/' {
        let loc = self.loc;

        c = next!({
          return Some(Err(Err::new(srcloc!(), loc, ErrKind::CommentEOF)));
        });

        if c != b'/' {
          return Some(Err(Err::new(srcloc!(), loc, ErrKind::CommentByte(c))));
        }

        loop {
          c = next!({ return None });

          if c == b'\n' {
            continue 'LOOP;
          }
        }
      } else if c == b'@' {
        let loc = self.loc;
        c = next!({ return Some(Err(Err::new(srcloc!(), loc, ErrKind::AddrEOF))) });

        let mut len = 1;
        if c.is_ascii_digit() {
          loop {
            c = next!({ break });

            if !c.is_ascii_digit() {
              if !c.is_ascii_whitespace() {
                return Some(Err(Err::new(srcloc!(), loc, ErrKind::AddrNumByte(c))));
              }

              break;
            }

            len += 1;
          }

        // let tok = self.buf
        } else if Label::is_label_start(c) {
        }

        //   if c.is_ascii_digit() {
        //     loop {
        //       c = next!(self, { break });

        //       if !c.is_ascii_digit() {
        //         if !c.is_ascii_whitespace() {
        //           return Some(Err(unexpected_byte!(
        //             self.loc,
        //             c,
        //             "whitespace to create a numerical address"
        //           )));
        //         }

        //         break;
        //       }

        //       text.push(c);
        //     }

        //     // 32767 (15 bits of address value)
        //     let addr = if let Some(addr) = crate::utils::atoi(&text, 32767) {
        //       addr
        //     } else {
        //       return Some(Ok(addr_range!(
        //         loc,
        //         inst::text_str(&text),
        //         32767,
        //         "a numerical address within range"
        //       )));
        //     };

        //     return Some(Ok(Inst::AddrNum(loc, addr)));
        //   } else if is_label_start(c) {
        //     let mut text: Text = smallvec![c];

        //     loop {
        //       c = next!({ break });

        //       if !is_label_byte(c) {
        //         if !c.is_ascii_whitespace() {
        //           return asm_lex_unexpected!(
        //             self.loc,
        //             c,
        //             "whitespace to create a label address"
        //           );
        //         }

        //         break;
        //       }

        //       text.push(c);
        //     }

        //     return Some(Ok(Inst::addr_label(loc, text)));
        //   } else {
        //     return asm_lex_unexpected!(self.loc, c, MSG);
        //   }
        // } else if c == b'(' {
        //   let loc = self.loc;
        //   const MSG: &str = "a label";
        //   c = next!({ return asm_lex_eof!(self.loc, MSG) });

        //   if is_label_start(c) {
        //     let mut text: Text = smallvec![c];

        //     loop {
        //       c = next!({ return asm_lex_eof!(self.loc, "a closing parenthesis") });

        //       if !is_label_byte(c) {
        //         if c == b')' {
        //           break;
        //         }

        //         return asm_lex_unexpected!(self.loc, c, "a label or closing parenthesis");
        //       }

        //       text.push(c);
        //     }

        //     return Some(Ok(Inst::Label(loc, text)));
        //   } else {
        //     return asm_lex_unexpected!(self.loc, c, MSG);
        //   }
        // } else {
        //   let dest_loc = self.loc;
        //   const MSG: &str = "a destination or computation";
        //   c = next!({ return asm_lex_eof!(self.loc, MSG) });

        //   let mut text: Text = smallvec![c];
        //   loop {
        //     c = next!({ return asm_lex_eof!(self.loc, MSG) });

        //     if c == b'=' {
        //       let dest = if let Ok(dest) = Dest::try_from((&text, dest_loc)) {
        //         dest
        //       } else {
        //         return asm_lex_unexpected_tok!(
        //           dest_loc,
        //           unsafe { String::from_utf8_unchecked(text.to_vec()) },
        //           "a destination"
        //         );
        //       };

        //       let loc = self.loc;
        //       const MSG: &str = "a computation";
        //       c = next!({ return asm_lex_eof!(self.loc, MSG) });

        //       let mut text: Text = smallvec![c];
        //       loop {
        //         c = next!({
        //           if let Ok(comp) = Comp::try_from((&text, loc)) {
        //             return Some(Ok(Inst::Assign(dest_loc, dest, comp)));
        //           } else {
        //             return asm_lex_unexpected_tok!(
        //               loc,
        //               unsafe { String::from_utf8_unchecked(text.to_vec()) },
        //               MSG
        //             );
        //           }
        //         });

        //         if c.is_ascii_whitespace() {
        //           if let Ok(comp) = Comp::try_from((&text, loc)) {
        //             return Some(Ok(Inst::Assign(dest_loc, dest, comp)));
        //           } else {
        //             return asm_lex_unexpected_tok!(
        //               loc,
        //               unsafe { String::from_utf8_unchecked(text.to_vec()) },
        //               MSG
        //             );
        //           }
        //         } else if c == b';' {
        //           let loc = self.loc;
        //           const MSG: &str = "a jump";
        //           c = next!({ return asm_lex_eof!(self.loc, MSG) });

        //           let mut text: Text = smallvec![c];
        //           loop {
        //             c = next!({
        //               if let Ok(jump) = Jump::try_from((&text, loc)) {
        //                 return Some(Ok(Inst::Inst(dest_loc, dest, comp, jump)));
        //               } else {
        //                 return asm_lex_unexpected_tok!(
        //                   loc,
        //                   unsafe { String::from_utf8_unchecked(text.to_vec()) },
        //                   MSG
        //                 );
        //               }
        //             });
        //           }
        //         }

        //         text.push(c);
        //       }
        //     } else if c == b';' {
        //       let comp = if let Ok(comp) = Comp::try_from((&text, loc)) {
        //         comp
        //       } else {
        //         return asm_lex_unexpected_tok!(
        //           loc,
        //           unsafe { String::from_utf8_unchecked(text.to_vec()) },
        //           "a computation"
        //         );
        //       };
        //     }

        //     text.push(c);
        //   }

        // return asm_lex_unexpected!(self.loc, c, "an instruction");
      }
    }
  }
}

// #[cfg(test)]
// mod tests {
//   use super::Lex;
//   use crate::inst::Comp;
//   use crate::inst::Dest;
//   use crate::inst::Inst;
//   use crate::inst::Jump;
//   use crate::inst::Text;
//   use crate::loc;
//   use crate::utils::loc::Loc;
//   use std::io::Read;

//   macro_rules! lex {
//     ($f:expr) => {
//       Lex::from(include_bytes!(concat!("../../tests/data/", $f)).bytes())
//     };
//   }

//   macro_rules! next {
//     ($lex:expr, $inst:expr) => {
//       assert_eq!($lex.next(), Some(Ok($inst)));
//     };
//   }

//   #[test]
//   fn empty() {
//     let mut lex = lex!("empty");
//     assert_eq!(lex.loc, Loc::new(1, 0));
//     assert_eq!(lex.next(), None);
//     assert_eq!(lex.loc, Loc::new(1, 0));
//   }

//   #[test]
//   fn spaces() {
//     let mut lex = lex!("spaces");
//     assert_eq!(lex.next(), None);
//     assert_eq!(lex.loc, Loc::new(5, 0));
//   }

//   #[test]
//   fn comments() {
//     let mut lex = lex!("comments");
//     assert_eq!(lex.next(), None);
//     assert_eq!(lex.loc, Loc::new(5, 0));
//   }

//   #[test]
//   fn addr_nums() {
//     let mut lex = lex!("addr_nums");
//     next!(lex, Inst::AddrNum(loc!(3, 5), 8192));
//     next!(lex, Inst::AddrNum(loc!(5, 1), 123));
//     next!(lex, Inst::AddrNum(loc!(9, 5), 556));
//     assert_eq!(lex.next(), None);
//   }

//   macro_rules! label {
//     ($label:path, $line:expr, $col:expr, $text:expr) => {
//       $label(loc!($line, $col), Text::from_slice($text))
//     };
//   }

//   #[test]
//   fn address_labels() {
//     let mut lex = lex!("addr_labels");
//     next!(lex, label!(Inst::AddrLabel, 3, 5, b"FOO"));
//     next!(lex, label!(Inst::AddrLabel, 5, 1, b"BARBAZ"));
//     next!(lex, Inst::AddrKBD(loc!(9, 5)));
//     next!(lex, label!(Inst::AddrLabel, 11, 1, b"BAZOO"));
//     next!(lex, Inst::AddrLCL(loc!(13, 1)));
//     next!(lex, label!(Inst::AddrLabel, 13, 6, b"LCLCL"));
//     next!(lex, Inst::AddrSCREEN(loc!(14, 1)));
//     next!(lex, Inst::AddrSP(loc!(14, 9)));
//     next!(lex, label!(Inst::AddrLabel, 14, 13, b"SPP"));
//     next!(lex, Inst::AddrARG(loc!(15, 1)));
//     next!(lex, label!(Inst::AddrLabel, 15, 6, b"ARG0"));
//     next!(lex, Inst::AddrTHIS(loc!(16, 1)));
//     next!(lex, Inst::AddrTHAT(loc!(16, 7)));
//     next!(lex, label!(Inst::AddrLabel, 16, 13, b"THOSE"));
//     next!(lex, Inst::AddrR0(loc!(17, 1)));
//     next!(lex, Inst::AddrR1(loc!(17, 5)));
//     next!(lex, Inst::AddrR11(loc!(17, 9)));
//     next!(lex, label!(Inst::AddrLabel, 17, 14, b"R1_hello"));
//     next!(lex, label!(Inst::AddrLabel, 17, 24, b"R11_hello"));
//     assert_eq!(lex.next(), None);
//   }

//   #[test]
//   fn label() {
//     let mut lex = lex!("label");
//     next!(lex, label!(Inst::AddrLabel, 3, 5, b"FOO"));
//     next!(lex, label!(Inst::Label, 5, 1, b"LABEL"));
//     next!(lex, label!(Inst::AddrLabel, 9, 5, b"LABEL"));
//     next!(lex, label!(Inst::AddrLabel, 11, 1, b"BAR"));
//     next!(lex, label!(Inst::Label, 13, 1, b"BAR"));
//     next!(lex, label!(Inst::AddrLabel, 15, 1, b"LAB0"));
//     next!(lex, label!(Inst::Label, 17, 1, b"LAB0"));
//     assert_eq!(lex.next(), None);
//   }

// #[test]
// fn assignments() {
//   let mut scanner = scanner!("assignments");
//   assert_next!(
//     scanner,
//     Token::Assignment(Destination::A, Computation::MMinus1),
//     Location::new(1, 1)
//   );
//   assert_next!(
//     scanner,
//     Token::Assignment(Destination::AM, Computation::DOrA),
//     Location::new(2, 1)
//   );
//   assert_next!(
//     scanner,
//     Token::Assignment(Destination::AMD, Computation::APlus1),
//     Location::new(3, 1)
//   );
//   assert_eq!(scanner.next(), None);
// }

// #[test]
// fn branches() {
//   let mut scanner = scanner!("branches");
//   assert_next!(scanner, tbuf, Token::Comp(Comp::MMinus1));
//   assert_eq!(scanner.token_pos(), Location::new(1, 1));
//   assert_next!(scanner, tbuf, Token::Semi);
//   assert_eq!(scanner.token_pos(), Location::new(1, 4));
//   assert_next!(scanner, tbuf, Token::Jump(Jump::JEQ));
//   assert_eq!(scanner.token_pos(), Location::new(1, 5));
//   assert_next!(scanner, tbuf, Token::Comp(Comp::DOrA));
//   assert_eq!(scanner.token_pos(), Location::new(2, 1));
//   assert_next!(scanner, tbuf, Token::Semi);
//   assert_eq!(scanner.token_pos(), Location::new(2, 4));
//   assert_next!(scanner, tbuf, Token::Jump(Jump::JNE));
//   assert_eq!(scanner.token_pos(), Location::new(2, 5));
//   assert_next!(scanner, tbuf, Token::Comp(Comp::APlus1));
//   assert_eq!(scanner.token_pos(), Location::new(3, 1));
//   assert_next!(scanner, tbuf, Token::Semi);
//   assert_eq!(scanner.token_pos(), Location::new(3, 4));
//   assert_next!(scanner, tbuf, Token::Jump(Jump::JMP));
//   assert_eq!(scanner.token_pos(), Location::new(3, 5));
//   assert_eq!(scanner.next(), None);
// }

// #[test]
// fn instructions() {
//   let mut scanner = scanner!("instructions");
//   assert_next!(scanner, tbuf, Token::Dest(Dest::A));
//   assert_eq!(scanner.token_pos(), Location::new(1, 1));
//   assert_next!(scanner, tbuf, Token::Comp(Comp::MMinus1));
//   assert_eq!(scanner.token_pos(), Location::new(1, 3));
//   assert_next!(scanner, tbuf, Token::Semi);
//   assert_eq!(scanner.token_pos(), Location::new(1, 6));
//   assert_next!(scanner, tbuf, Token::Jump(Jump::JEQ));
//   assert_eq!(scanner.token_pos(), Location::new(1, 7));
//   assert_next!(scanner, tbuf, Token::Dest(Dest::AM));
//   assert_eq!(scanner.token_pos(), Location::new(2, 1));
//   assert_next!(scanner, tbuf, Token::Comp(Comp::DOrA));
//   assert_eq!(scanner.token_pos(), Location::new(2, 4));
//   assert_next!(scanner, tbuf, Token::Semi);
//   assert_eq!(scanner.token_pos(), Location::new(2, 7));
//   assert_next!(scanner, tbuf, Token::Jump(Jump::JNE));
//   assert_eq!(scanner.token_pos(), Location::new(2, 8));
//   assert_next!(scanner, tbuf, Token::Dest(Dest::AMD));
//   assert_eq!(scanner.token_pos(), Location::new(3, 1));
//   assert_next!(scanner, tbuf, Token::Comp(Comp::APlus1));
//   assert_eq!(scanner.token_pos(), Location::new(3, 5));
//   assert_next!(scanner, tbuf, Token::Semi);
//   assert_eq!(scanner.token_pos(), Location::new(3, 8));
//   assert_next!(scanner, tbuf, Token::Jump(Jump::JMP));
//   assert_eq!(scanner.token_pos(), Location::new(3, 9));
//   assert_eq!(scanner.next(), None);
// }
//}

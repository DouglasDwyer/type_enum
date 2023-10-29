# type_enum

[![Crates.io](https://img.shields.io/crates/v/type_enum.svg)](https://crates.io/crates/type_enum)
[![Docs.rs](https://docs.rs/type_enum/badge.svg)](https://docs.rs/type_enum)
![Nightly](https://img.shields.io/badge/nightly-required-red)


`type_enum` provides an ergonomic and non-intrusive way to:
- Create tagged unions consisting of different types
- Execute trait methods common to all type variants on those unions
- Match on type variants to recover the original type

This crate requires nightly Rust.

### Example

```rust
use type_enum::*;

type Good = type_list! { u8, i32, String };

let val = TypeEnum::<Good>::new(-23);

// Enums may be cast to any trait common among all enum variants.
println!("{}", val.cast::<dyn ToString>().to_string());

// Enums may be matched to obtain the original type.
let abs = type_match(val)
    .with::<u8>(|x| x as i32)
    .with::<i32>(|x| x.abs())
    .otherwise(|| 0)
    .get();

println!("{abs}");
```

### Why not use a normal enum?

While Rust's enum types are incredibly powerful, they place the burden of extending functionality and implementing new traits on the enum definition. For instance, consider the following code snippet:

```rust
pub enum Bad { U8(u8), U16(u16), String(String) }

pub trait NewBehavior {}
impl NewBehavior for u8 {}
impl NewBehavior for u16 {}
impl NewBehavior for String {}
```

Even though all three constituent types implement `NewBehavior`, the enum does not. Adding functionality to the enum requires modifying its definition; it does not inherit behavior from its variants. If `Bad` and `NewBehavior` were defined in separate crates, implementing `NewBehavior` on `Bad` might even be impossible. `type_enum` reverses this - the traits usable on a `TypeEnum` are inherited from the variants. This allows for extending code by modifying and maintaining the type variants alone.

## Optional features

**serde** - Allows for the serialization of `TypeEnum` instances when all variants are serializable.
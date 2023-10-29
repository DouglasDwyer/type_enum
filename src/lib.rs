#![feature(arbitrary_self_types)]
#![feature(const_heap)]
#![feature(const_maybe_uninit_as_mut_ptr)]
#![feature(const_mut_refs)]
#![feature(const_slice_index)]
#![feature(const_ptr_read)]
#![feature(const_ptr_write)]
#![feature(const_type_id)]
#![feature(core_intrinsics)]
#![feature(downcast_unchecked)]
#![feature(unsize)]
#![allow(clippy::no_effect)]
#![allow(path_statements)]
#![deny(warnings)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

//! `type_enum` provides an ergonomic and non-intrusive way to:
//! - Create tagged unions consisting of different types
//! - Execute trait methods common to all type variants on those unions
//! - Match on type variants to recover the original type
//!
//! This crate requires nightly Rust.
//!
//! ### Example
//!
//! ```rust
//! use type_enum::*;
//!
//! type Good = type_list! { u8, i32, String };
//!
//! let val = TypeEnum::<Good>::new(-23);
//!
//! // Enums may be cast to any trait common among all enum variants.
//! println!("{}", val.cast::<dyn ToString>().to_string());
//!
//! // Enums may be matched to obtain the original type.
//! let abs = type_match(val)
//!     .with::<u8>(|x| x as i32)
//!     .with::<i32>(|x| x.abs())
//!     .otherwise(|| 0)
//!     .get();
//!
//! println!("{abs}");
//! ```
//!
//! ### Why not use a normal enum?
//!
//! While Rust's enum types are incredibly powerful, they place the burden of extending functionality and implementing new traits on the enum definition. For instance, consider the following code snippet:
//!
//! ```rust
//! pub enum Bad { U8(u8), U16(u16), String(String) }
//!
//! pub trait NewBehavior {}
//! impl NewBehavior for u8 {}
//! impl NewBehavior for u16 {}
//! impl NewBehavior for String {}
//! ```
//!
//! Even though all three constituent types implement `NewBehavior`, the enum does not. Adding functionality to the enum requires modifying its definition; it does not inherit behavior from its variants. If `Bad` and `NewBehavior` were defined in separate crates, implementing `NewBehavior` on `Bad` might even be impossible. `type_enum` reverses this - the traits usable on a `TypeEnum` are inherited from the variants. This allows for extending code by modifying and maintaining the type variants alone.

use const_list::*;
use private::*;
use std::any::*;
use std::marker::*;
use std::mem::*;
use std::ops::*;
use std::slice::*;

#[cfg(feature = "serde")]
/// Implements serialization and deserialization for type enums.
mod serialize;

/// Creates a list of types that may be used to identify a type enum.
#[macro_export]
macro_rules! type_list {
    {} => { EmptyDescriptor };
    { $first: ty } => { ConsDescriptor<$first, EmptyDescriptor> };
    { $first: ty, $($ty: ty),+ } => {
        ConsDescriptor<$first, type_list! { $($ty),* }>
    }
}

/// Stores one out of a set number of types.
pub struct TypeEnum<D: TypeEnumDescriptor> {
    /// The variant of this type enum.
    variant: u8,
    /// The value of the type enum.
    value: MaybeUninit<D::EnumBacking>,
}

impl<D: TypeEnumDescriptor> TypeEnum<D> {
    /// Creates a new type enum for the given value.
    pub const fn new<T: 'static>(value: T) -> Self {
        unsafe {
            EnsureNoDuplicates::<D>::VALUE;
            let variant = VariantId::<T, D>::VALUE;
            let mut res = MaybeUninit::<D::EnumBacking>::uninit();
            res.as_mut_ptr().cast::<T>().write(value);

            Self {
                variant,
                value: res,
            }
        }
    }

    /// Coerces the value within this enum to an unsized type reference.
    pub const fn cast<U: ?Sized>(&self) -> &U
    where
        D: Castable<U>,
    {
        unsafe { &*self.cast_raw::<U>() }
    }

    /// Coerces the value within this enum to a mutable unsized type reference.
    pub const fn cast_mut<U: ?Sized>(&mut self) -> &mut U
    where
        D: Castable<U>,
    {
        unsafe { &mut *(self.cast_raw::<U>() as *mut _) }
    }

    /// Downcasts this value to a discrete type, or returns `self` if the enum variant was not `T`.
    pub fn downcast<T: 'static>(self) -> Result<T, Self> {
        unsafe {
            if self.variant == VariantId::<T, D>::VALUE {
                Ok(self.downcast_unchecked())
            } else {
                Err(self)
            }
        }
    }

    /// Downcasts this value to a discrete type, without performing any checks.
    ///
    /// # Safety
    ///
    /// For this function call to be sound, this type enum must have been created with a `T` value.
    pub unsafe fn downcast_unchecked<T: 'static>(self) -> T {
        VariantId::<T, D>::VALUE;
        self.value.as_ptr().cast::<T>().read()
    }

    /// Coerces this type enum to an unsized type, and returns a raw pointer to the value.
    const fn cast_raw<U: ?Sized>(&self) -> *const U
    where
        D: Castable<U>,
    {
        unsafe {
            let virtual_pointer =
                *<D as AllCoercible<U>>::COERCION_POINTERS.get_unchecked(self.variant as usize);
            let res = (self.value.as_ptr() as *const (), virtual_pointer);
            (&res as *const (*const (), *const ())).cast::<&U>().read()
        }
    }
}

impl<D: TypeEnumDescriptor> Drop for TypeEnum<D> {
    fn drop(&mut self) {
        unsafe {
            std::ptr::drop_in_place(self.cast_raw::<dyn Any>() as *mut dyn Any);
        }
    }
}

impl<D: TypeEnumDescriptor + Castable<dyn TypeEnumClone<D>>> Clone for TypeEnum<D> {
    fn clone(&self) -> Self {
        self.cast::<dyn TypeEnumClone<D>>().clone_enum()
    }
}

impl<D: TypeEnumDescriptor + Castable<dyn std::fmt::Debug>> std::fmt::Debug for TypeEnum<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.cast::<dyn std::fmt::Debug>().fmt(f)
    }
}

impl<D: TypeEnumDescriptor + Castable<dyn SelfPartialEq>> PartialEq for TypeEnum<D> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            self.variant == other.variant
                && self
                    .cast::<dyn SelfPartialEq>()
                    .partial_eq(other.value.as_ptr() as *const ())
        }
    }
}

impl<D: TypeEnumDescriptor + Castable<dyn SelfPartialEq> + Castable<dyn SelfEq>> Eq
    for TypeEnum<D>
{
}

impl<D: TypeEnumDescriptor + Castable<dyn Any>> Deref for TypeEnum<D> {
    type Target = dyn Any;

    fn deref(&self) -> &Self::Target {
        self.cast()
    }
}

impl<D: TypeEnumDescriptor + Castable<dyn Any>> DerefMut for TypeEnum<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.cast_mut()
    }
}

impl<U: ?Sized, D: TypeEnumDescriptor + Castable<U>> AsRef<U> for TypeEnum<D> {
    fn as_ref(&self) -> &U {
        self.cast()
    }
}

/// Computes the index of a type within a list descriptor.
struct VariantId<T: 'static, D: ListDescriptor>(PhantomData<fn() -> (T, D)>);

impl<T: 'static, D: ListDescriptor> VariantId<T, D> {
    /// The value of the index of `T` within the list `D`.
    pub const VALUE: u8 = Self::index_of();

    /// Computes the index of a variant.
    const fn index_of() -> u8 {
        let mut i = 0;
        while i < D::IDS.len() {
            if let Some(x) = D::IDS.get(i) {
                if type_ids_eq(x, &TypeId::of::<T>()) {
                    return i as u8;
                }
            } else {
                unreachable!();
            }
            i += 1;
        }
        panic!("Type not found in enum variants.")
    }
}

/// A list that contains no types.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct EmptyDescriptor;

impl ListDescriptor for EmptyDescriptor {
    type EnumBacking = ();
    const IDS: ConstList<'static, TypeId> = ConstList::new();
}

impl<U: ?Sized> AllCoercible<U> for EmptyDescriptor {
    const COERCION_POINTERS: &'static [*const ()] = &[];
}

/// A list that contains one or more types, split into a first and rest.
pub struct ConsDescriptor<F: 'static, R: ListDescriptor>(PhantomData<fn() -> (F, R)>);

impl<F: 'static, R: ListDescriptor> Copy for ConsDescriptor<F, R> {}

impl<F: 'static, R: ListDescriptor> Clone for ConsDescriptor<F, R> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<F: 'static, R: ListDescriptor> std::fmt::Debug for ConsDescriptor<F, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ConsDescriptor").finish()
    }
}

impl<F: 'static, R: ListDescriptor> Default for ConsDescriptor<F, R> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<F: 'static, R: ListDescriptor> PartialEq for ConsDescriptor<F, R> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl<F: 'static, R: ListDescriptor> Eq for ConsDescriptor<F, R> {}

impl<F: 'static, R: ListDescriptor> ListDescriptor for ConsDescriptor<F, R> {
    type EnumBacking = LinkedUnion<F, R::EnumBacking>;
    const IDS: ConstList<'static, TypeId> = R::IDS.push(TypeId::of::<F>());
}

impl<F: 'static, R: ListDescriptor> NonemptyListDescriptor for ConsDescriptor<F, R> {
    type First = F;
    type Rest = R;
}

impl<U: ?Sized, F: 'static + Unsize<U>, R: ListDescriptor + AllCoercible<U>> AllCoercible<U>
    for ConsDescriptor<F, R>
{
    const COERCION_POINTERS: &'static [*const ()] = push_const_array(
        coercion_pointer::<U, F>(),
        <R as AllCoercible<U>>::COERCION_POINTERS,
    );
}

/// Creates a new compile-time array with the specified value pushed to the front.
const fn push_const_array<T: Copy>(value: T, arr: &[T]) -> &'static [T] {
    unsafe {
        let values = std::intrinsics::const_allocate(
            (arr.len() + 1) * std::mem::size_of::<T>(),
            std::mem::align_of::<T>(),
        ) as *mut T;
        std::ptr::copy_nonoverlapping(arr.as_ptr(), values.add(1), arr.len());
        values.write(value);
        from_raw_parts(values, arr.len() + 1)
    }
}

/// Gets the virtual table pointer for coercions from `F` to `U`.
const fn coercion_pointer<U: ?Sized, F: 'static + Unsize<U>>() -> *const () {
    unsafe {
        let x: *const F = std::ptr::null();
        let u: *const U = x;
        ((&u as *const *const U) as *const *const ()).add(1).read()
    }
}

/// Determines whether two type IDs are equivalent at compile time.
const fn type_ids_eq(a: &TypeId, b: &TypeId) -> bool {
    unsafe { arrays_eq(transmute::<_, &[u8; size_of::<TypeId>()]>(a), transmute(b)) }
}

/// Determines whether the two given arrays are equal.
const fn arrays_eq<const N: usize>(a: &[u8; N], b: &[u8; N]) -> bool {
    let mut i = 0;
    while i < N {
        if a[i] != b[i] {
            return false;
        }

        i += 1;
    }
    true
}

impl<'a, D: ListDescriptor> TypeMatchable for &'a TypeEnum<D> {
    type Descriptor = D;
    type Output<T: 'static> = &'a T;

    fn variant(&self) -> u8 {
        self.variant
    }

    unsafe fn downcast_unchecked<T: 'static>(self) -> Self::Output<T> {
        (**self).downcast_ref_unchecked()
    }
}

impl<'a, D: ListDescriptor> TypeMatchable for &'a mut TypeEnum<D> {
    type Descriptor = D;
    type Output<T: 'static> = &'a mut T;

    fn variant(&self) -> u8 {
        self.variant
    }

    unsafe fn downcast_unchecked<T: 'static>(self) -> Self::Output<T> {
        self.downcast_mut_unchecked()
    }
}

impl<D: ListDescriptor> TypeMatchable for TypeEnum<D> {
    type Descriptor = D;
    type Output<T: 'static> = T;

    fn variant(&self) -> u8 {
        self.variant
    }

    unsafe fn downcast_unchecked<T: 'static>(self) -> Self::Output<T> {
        TypeEnum::downcast_unchecked(self)
    }
}

/// Begins matching based upon the backing type of a type enum.
pub fn type_match<M: TypeMatchable, O>(m: M) -> TypeMatch<M, O, Exhaustive, EmptyDescriptor> {
    TypeMatch {
        data: PhantomData,
        matcher: Some(m),
        output: None,
    }
}

/// Allows for matching the variants of a `TypeEnum`.
pub struct TypeMatch<M: TypeMatchable, O, E: CaseRequirement, L: TypeEnumDescriptor> {
    /// A marker object.
    data: PhantomData<fn(M, O, E, L)>,
    /// The object with which to match.
    matcher: Option<M>,
    /// The result of matching, if any so far.
    output: Option<O>,
}

impl<M: TypeMatchable, O, L: TypeEnumDescriptor> TypeMatch<M, O, Exhaustive, L> {
    /// Adds a case to this type match. Unless `otherwise` is called, all type variants must be present for compilation to succeed.
    pub fn with<T: 'static>(
        self,
        f: impl FnOnce(M::Output<T>) -> O,
    ) -> TypeMatch<M, O, Exhaustive, ConsDescriptor<T, L>> {
        unsafe {
            if Some(VariantId::<T, M::Descriptor>::VALUE)
                == self.matcher.as_ref().map(|x| x.variant())
            {
                TypeMatch {
                    data: PhantomData,
                    matcher: None,
                    output: Some(f(self.matcher.unwrap_unchecked().downcast_unchecked::<T>())),
                }
            } else {
                TypeMatch {
                    data: PhantomData,
                    matcher: self.matcher,
                    output: self.output,
                }
            }
        }
    }

    /// Adds a catch-all case to the end of a type match.
    pub fn otherwise(self, f: impl FnOnce() -> O) -> TypeMatch<M, O, Nonexhaustive, L> {
        if self.output.is_none() {
            TypeMatch {
                data: PhantomData,
                matcher: None,
                output: Some(f()),
            }
        } else {
            TypeMatch {
                data: PhantomData,
                matcher: None,
                output: self.output,
            }
        }
    }
}

impl<M: TypeMatchable, O, L: ListDescriptor> TypeMatch<M, O, Exhaustive, L> {
    /// Gets the result of the type match.
    pub fn get(self) -> O {
        EnsureListSubset::<L, M::Descriptor>::VALUE;
        EnsureListSubset::<M::Descriptor, L>::VALUE;
        unsafe { self.output.unwrap_unchecked() }
    }
}

impl<M: TypeMatchable, O, L: ListDescriptor> TypeMatch<M, O, Nonexhaustive, L> {
    /// Gets the result of the type match.
    pub fn get(self) -> O {
        EnsureListSubset::<L, M::Descriptor>::VALUE;
        unsafe { self.output.unwrap_unchecked() }
    }
}

/// Ensures that a type list has no duplicate items.
struct EnsureNoDuplicates<D: ListDescriptor>(PhantomData<fn() -> D>);

impl<D: ListDescriptor> EnsureNoDuplicates<D> {
    /// Invocations of this constant ensure the invariant is upheld.
    const VALUE: () = Self::ensure();

    /// Ensures that the invariant is upheld.
    const fn ensure() {
        assert!(D::IDS.len() < 256, "Maximum type variants exceeded.");
        let mut i = 0;
        while i < D::IDS.len() {
            let mut j = i + 1;
            while j < D::IDS.len() {
                match (D::IDS.get(i), D::IDS.get(j)) {
                    (Some(x), Some(y)) => {
                        assert!(!type_ids_eq(x, y), "Type list contains duplicates.")
                    }
                    _ => unreachable!(),
                }

                j += 1;
            }
            i += 1;
        }
    }
}

/// Ensures that `A` is a subset of `B`.
struct EnsureListSubset<A: ListDescriptor, B: ListDescriptor>(PhantomData<fn() -> (A, B)>);

impl<A: ListDescriptor, B: ListDescriptor> EnsureListSubset<A, B> {
    /// Invocations of this constant ensure the invariant is upheld.
    const VALUE: () = Self::ensure();

    /// Ensures that the invariant is upheld.
    const fn ensure() {
        let mut i = 0;
        while i < A::IDS.len() {
            let mut found = false;
            let mut j = 0;
            while j < B::IDS.len() {
                match (A::IDS.get(i), B::IDS.get(j)) {
                    (Some(a), Some(b)) => {
                        if type_ids_eq(a, b) {
                            found = true;
                            break;
                        }
                    }
                    _ => unreachable!(),
                }
                j += 1;
            }

            if !found {
                panic!("List was not subset of the other.");
            }

            i += 1;
        }
    }
}

/// Allows an object to be cloned while wrapped in a type enum.
trait TypeEnumClone<D: TypeEnumDescriptor>: 'static {
    /// Clones this object into a new type enum.
    fn clone_enum(&self) -> TypeEnum<D>;
}

impl<T: 'static + Clone, D: TypeEnumDescriptor> TypeEnumClone<D> for T {
    fn clone_enum(&self) -> TypeEnum<D> {
        TypeEnum::new(self.clone())
    }
}

/// Allows an object to be compared while wrapped in a type enum.
trait SelfPartialEq: 'static {
    /// Determines whether this object equals another of the same time.
    ///
    /// # Safety
    ///
    /// For this method to be sound, `other` must point to
    /// a valid instance of type `Self`.
    unsafe fn partial_eq(&self, other: *const ()) -> bool;
}

impl<T: 'static + PartialEq> SelfPartialEq for T {
    unsafe fn partial_eq(&self, other: *const ()) -> bool {
        self == &*(other as *const _)
    }
}

/// Marks an object as obeying strict equality while wrapped in a type enum.
trait SelfEq: 'static {}

impl<T: 'static + Eq> SelfEq for T {}

/// A list of type variants.
pub trait TypeEnumDescriptor: ListDescriptor {}

impl<T: ListDescriptor> TypeEnumDescriptor for T {}

/// A list of type variants that may be coerced to the given unsized type.
pub trait Castable<U: ?Sized>: AllCoercible<U> {}

impl<U: ?Sized, T: AllCoercible<U>> Castable<U> for T {}

/// Hides implementation-related traits.
mod private {
    use super::*;

    /// A list of type variants.
    pub trait ListDescriptor:
        'static + Copy + Clone + std::fmt::Debug + Default + PartialEq + Eq + AllCoercible<dyn Any>
    {
        /// An enum type that is big enough to hold any variant in this list.
        type EnumBacking;
        /// The list of type IDs within this descriptor.
        const IDS: ConstList<'static, TypeId>;
    }

    /// A non-empty list of type variants.
    pub trait NonemptyListDescriptor: ListDescriptor {
        /// The first type in the list.
        type First: 'static;
        /// The rest of the list.
        type Rest: ListDescriptor;
    }

    /// Marks lists for which all enum variants are coercible to `U`.
    pub trait AllCoercible<U: ?Sized> {
        /// The list of virtual table pointers for converting between types.
        const COERCION_POINTERS: &'static [*const ()];
    }

    /// A union type that can be chained to hold variants within a type enum.
    pub union LinkedUnion<A, B> {
        /// The first item.
        _a: ManuallyDrop<A>,
        /// The rest of the union.
        _b: ManuallyDrop<B>,
    }

    /// Marks a type that can be matched with `type_match`.
    pub trait TypeMatchable {
        /// The list of variants for this type.
        type Descriptor: ListDescriptor;
        /// The output provided for a given type.
        type Output<T: 'static>;

        /// The variant index of this matcher.
        fn variant(&self) -> u8;

        /// Downcasts this value to the given type.
        ///
        /// # Safety
        ///
        /// For this type to be sound, the type enum must be of the correct variant.
        unsafe fn downcast_unchecked<T: 'static>(self) -> Self::Output<T>;
    }

    /// Marks a match where all cases must be covered.
    pub struct Exhaustive;

    impl CaseRequirement for Exhaustive {}

    /// Marks a match which has a catch-all.
    pub struct Nonexhaustive;

    impl CaseRequirement for Nonexhaustive {}

    /// Describes which cases must be included in a match.
    pub trait CaseRequirement {}
}

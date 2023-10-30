use crate::*;
use serde::*;

impl<D: TypeEnumDescriptor + SerializeCastable> Serialize for TypeEnum<D> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::*;

        unsafe {
            let mut seq = serializer.serialize_seq(Some(2))?;
            seq.serialize_element(&self.variant)?;
            let virtual_pointer =
                *<D::AsSerialize<S> as AllCoercible<dyn SerializeInto<S>>>::COERCION_POINTERS
                    .get_unchecked(self.variant as usize);
            let res = (self.value.as_ptr() as *const (), virtual_pointer);
            let r = (&res as *const (*const (), *const ()))
                .cast::<&dyn SerializeInto<S>>()
                .read();
            r.serialize_into(&mut seq)?;
            seq.end()
        }
    }
}

impl<'a, Q: TypeEnumDescriptor + DeserializeCastable<'a, Q>> Deserialize<'a> for TypeEnum<Q> {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::*;

        /// Manages the deserialization process for a type enum.
        struct DeserializeEnumVisitor<'a, L: TypeEnumDescriptor + DeserializeCastable<'a, L>>(
            PhantomData<&'a L>,
        );

        impl<'a, L: TypeEnumDescriptor + DeserializeCastable<'a, L>> Visitor<'a>
            for DeserializeEnumVisitor<'a, L>
        {
            type Value = TypeEnum<L>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("Type sequence variant.")
            }

            fn visit_seq<A: SeqAccess<'a>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                unsafe {
                    let variant = seq.next_element::<u8>().and_then(|x| {
                        x.ok_or_else(|| <A::Error as Error>::custom("Expected variant value."))
                    })?;

                    let virtual_pointer = *<L::AsDeserialize<A> as AllCoercible<
                        dyn DeserializeInto<A, L>,
                    >>::COERCION_POINTERS
                        .get(variant as usize)
                        .ok_or_else(|| <A::Error as Error>::custom("Variant out-of-range."))?;

                    let res = (std::ptr::null(), virtual_pointer);
                    let r = (&res as *const (*const (), *const ()))
                        .cast::<*const dyn DeserializeInto<A, L>>()
                        .read();
                    <dyn DeserializeInto<A, L>>::deserialize_into(r, &mut seq)
                }
            }
        }

        deserializer.deserialize_seq(DeserializeEnumVisitor(PhantomData))
    }
}

/// Marks a type that may be serialized.
trait SerializeInto<S: Serializer> {
    /// Serializes the type into the given sequence.
    fn serialize_into(&self, serializer: &mut S::SerializeSeq) -> Result<(), S::Error>;
}

impl<S: Serializer, T: 'static + Serialize> SerializeInto<S> for T {
    fn serialize_into(&self, serializer: &mut S::SerializeSeq) -> Result<(), S::Error> {
        use serde::ser::*;
        serializer.serialize_element(self)
    }
}

/// Marks a type list for which all elements are serializable.
trait SerializeCastable: TypeEnumDescriptor {
    /// The type to use during serialization.
    type AsSerialize<S: Serializer>: Castable<dyn SerializeInto<S>> + TypeEnumDescriptor;
}

impl SerializeCastable for EmptyDescriptor {
    type AsSerialize<S: Serializer> = Self;
}

impl<T: 'static + Serialize, R: SerializeCastable> SerializeCastable for ConsDescriptor<T, R> {
    type AsSerialize<S: Serializer> = ConsDescriptor<T, R::AsSerialize<S>>;
}

/// Marks a type that may be deserialized.
trait DeserializeInto<'a, D: serde::de::SeqAccess<'a>, L: TypeEnumDescriptor> {
    /// Deserializes the type from the given sequence.
    fn deserialize_into(self: *const Self, deserializer: &mut D) -> Result<TypeEnum<L>, D::Error>;
}

impl<'a, D: serde::de::SeqAccess<'a>, T: 'static + Deserialize<'a>, L: TypeEnumDescriptor>
    DeserializeInto<'a, D, L> for T
{
    fn deserialize_into(self: *const Self, deserializer: &mut D) -> Result<TypeEnum<L>, D::Error> {
        Ok(TypeEnum::new(deserializer.next_element::<T>().and_then(
            |x| x.ok_or_else(|| <D::Error as serde::de::Error>::custom("Expected variant value.")),
        )?))
    }
}

/// Marks a type list for which all elements are deserializable.
trait DeserializeCastable<'a, L: TypeEnumDescriptor>: TypeEnumDescriptor {
    /// The type to use during deserialization.
    type AsDeserialize<D: serde::de::SeqAccess<'a>>: Castable<dyn DeserializeInto<'a, D, L>>
        + TypeEnumDescriptor;
}

impl<'a, L: TypeEnumDescriptor> DeserializeCastable<'a, L> for EmptyDescriptor {
    type AsDeserialize<S: serde::de::SeqAccess<'a>> = Self;
}

impl<'a, T: 'static + Deserialize<'a>, R: DeserializeCastable<'a, L>, L: TypeEnumDescriptor>
    DeserializeCastable<'a, L> for ConsDescriptor<T, R>
{
    type AsDeserialize<S: serde::de::SeqAccess<'a>> = ConsDescriptor<T, R::AsDeserialize<S>>;
}

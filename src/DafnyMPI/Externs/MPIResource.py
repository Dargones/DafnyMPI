import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count
import numpy as np

import module_ as module_
import _dafny as _dafny
import System_ as System_
import Std_Wrappers as Std_Wrappers
import Std_Concurrent as Std_Concurrent
import Std_FileIOInternalExterns as Std_FileIOInternalExterns
import Std_FileIO as Std_FileIO
import Std_BoundedInts as Std_BoundedInts
import Std_Base64 as Std_Base64
import Std_Relations as Std_Relations
import Std_Math as Std_Math
import Std_Collections_Seq as Std_Collections_Seq
import Std_Collections_Array as Std_Collections_Array
import Std_Collections_Imap as Std_Collections_Imap
import Std_Functions as Std_Functions
import Std_Collections_Iset as Std_Collections_Iset
import Std_Collections_Map as Std_Collections_Map
import Std_Collections_Set as Std_Collections_Set
import Std_Collections as Std_Collections
import Std_DynamicArray as Std_DynamicArray
import Std_Arithmetic_GeneralInternals as Std_Arithmetic_GeneralInternals
import Std_Arithmetic_MulInternalsNonlinear as Std_Arithmetic_MulInternalsNonlinear
import Std_Arithmetic_MulInternals as Std_Arithmetic_MulInternals
import Std_Arithmetic_Mul as Std_Arithmetic_Mul
import Std_Arithmetic_ModInternalsNonlinear as Std_Arithmetic_ModInternalsNonlinear
import Std_Arithmetic_DivInternalsNonlinear as Std_Arithmetic_DivInternalsNonlinear
import Std_Arithmetic_ModInternals as Std_Arithmetic_ModInternals
import Std_Arithmetic_DivInternals as Std_Arithmetic_DivInternals
import Std_Arithmetic_DivMod as Std_Arithmetic_DivMod
import Std_Arithmetic_Power as Std_Arithmetic_Power
import Std_Arithmetic_Logarithm as Std_Arithmetic_Logarithm
import Std_Arithmetic_Power2 as Std_Arithmetic_Power2
import Std_Strings_HexConversion as Std_Strings_HexConversion
import Std_Strings_DecimalConversion as Std_Strings_DecimalConversion
import Std_Strings_CharStrEscaping as Std_Strings_CharStrEscaping
import Std_Strings as Std_Strings
import Std_Unicode_Base as Std_Unicode_Base
import Std_Unicode_Utf8EncodingForm as Std_Unicode_Utf8EncodingForm
import Std_Unicode_Utf16EncodingForm as Std_Unicode_Utf16EncodingForm
import Std_Unicode_UnicodeStringsWithUnicodeChar as Std_Unicode_UnicodeStringsWithUnicodeChar
import Std_Unicode_Utf8EncodingScheme as Std_Unicode_Utf8EncodingScheme
import Std_Unicode as Std_Unicode
import Std_JSON_Values as Std_JSON_Values
import Std_JSON_Errors as Std_JSON_Errors
import Std_JSON_Spec as Std_JSON_Spec
import Std_JSON_Utils_Views_Core as Std_JSON_Utils_Views_Core
import Std_JSON_Utils_Views_Writers as Std_JSON_Utils_Views_Writers
import Std_JSON_Utils_Lexers_Core as Std_JSON_Utils_Lexers_Core
import Std_JSON_Utils_Lexers_Strings as Std_JSON_Utils_Lexers_Strings
import Std_JSON_Utils_Lexers as Std_JSON_Utils_Lexers
import Std_JSON_Utils_Cursors as Std_JSON_Utils_Cursors
import Std_JSON_Utils_Parsers as Std_JSON_Utils_Parsers
import Std_JSON_Grammar as Std_JSON_Grammar
import Std_JSON_ByteStrConversion as Std_JSON_ByteStrConversion
import Std_JSON_Serializer as Std_JSON_Serializer
import Std_JSON_Deserializer_Uint16StrConversion as Std_JSON_Deserializer_Uint16StrConversion
import Std_JSON_Deserializer as Std_JSON_Deserializer
import Std_JSON_ConcreteSyntax_Spec as Std_JSON_ConcreteSyntax_Spec
import Std_JSON_ConcreteSyntax_SpecProperties as Std_JSON_ConcreteSyntax_SpecProperties
import Std_JSON_ZeroCopy_Serializer as Std_JSON_ZeroCopy_Serializer
import Std_JSON_ZeroCopy_Deserializer_Core as Std_JSON_ZeroCopy_Deserializer_Core
import Std_JSON_ZeroCopy_Deserializer_Strings as Std_JSON_ZeroCopy_Deserializer_Strings
import Std_JSON_ZeroCopy_Deserializer_Numbers as Std_JSON_ZeroCopy_Deserializer_Numbers
import Std_JSON_ZeroCopy_Deserializer_ObjectParams as Std_JSON_ZeroCopy_Deserializer_ObjectParams
import Std_JSON_ZeroCopy_Deserializer_Objects as Std_JSON_ZeroCopy_Deserializer_Objects
import Std_JSON_ZeroCopy_Deserializer_ArrayParams as Std_JSON_ZeroCopy_Deserializer_ArrayParams
import Std_JSON_ZeroCopy_Deserializer_Arrays as Std_JSON_ZeroCopy_Deserializer_Arrays
import Std_JSON_ZeroCopy_Deserializer_Constants as Std_JSON_ZeroCopy_Deserializer_Constants
import Std_JSON_ZeroCopy_Deserializer_Values as Std_JSON_ZeroCopy_Deserializer_Values
import Std_JSON_ZeroCopy_Deserializer_API as Std_JSON_ZeroCopy_Deserializer_API
import Std_JSON_ZeroCopy_Deserializer as Std_JSON_ZeroCopy_Deserializer
import Std_JSON_ZeroCopy_API as Std_JSON_ZeroCopy_API
import Std_JSON_API as Std_JSON_API

# Module: MPIResource

class MPIResource:
    pass

class ArrayOfReals(MPIResource):
    def  __init__(self, length, val):
        self.arr = np.full(length, val, dtype=np.float64)

    def Length(self):
        return len(self.arr)
    
    def Get(self, i):
        return self.arr[i]
    
    def Set(self, i, val):
        self.arr[i] = val

    def GetContiguousView(self, fr, to):
      return self.arr[fr:to]

    def __dafnystr__(self) -> str:
        return "MPIResource.ArrayOfReals"

class ArrayOfReals2D(MPIResource):

    def  __init__(self, dim1, dim2, val):
        self.arr = np.full((dim1, dim2), val, dtype=np.float64)
        self.dim1 = dim1
        self.dim2 = dim2

    def Length(self):
        return self.dim1 * self.dim2
    
    def Dim1(self):
        return self.dim1
    
    def Dim2(self):
        return self.dim2
    
    def Get(self, i, j):
        return self.arr[i, j]
    
    def Set(self, i, j, val):
        self.arr[i, j] = val

    def GetContiguousView(self, fr, to):
      return self.arr.ravel()[fr:to]

    def __dafnystr__(self) -> str:
        return "MPIResource.ArrayOfReals2D"

import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count
from mpi4py import MPI

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
import MPIResource as MPIResource
import Arrays1D as Arrays1D

# Module: MPI

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetMPISize():
        return MPI.COMM_WORLD.Get_size()

class NatPlus:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        d_1_i_: int = source__
        return (d_1_i_) >= (-1)
    
class Handle:

    def __init__(self, handle):
        self.handle = handle

    def Wait(self):
        self.handle.wait()

class World:
    
    def  __init__(self, size):
        self._world = MPI.COMM_WORLD
        self._size = self._world.Get_size()
        if (self._size != size):
            print("You are running this code with wrong # of processes")
            sys.exit(1)
        self._rank = self._world.Get_rank()
        pass

    def __dafnystr__(self) -> str:
        return "MPI.World"
    
    @property
    def size(self):
        return self._size
    @property
    def rank(self):
        return self._rank
    
    def Send(self, res, fr, size, destination, tag):
        self._world.Send([res.GetContiguousView(fr, fr + size), MPI.DOUBLE], destination, tag)

    def Recv(self, res, fr, size, source, tag):
        self._world.Recv([res.GetContiguousView(fr, fr + size), MPI.DOUBLE], source, tag)

    def ISend(self, res, fr, size, destination, tag):
        handle = self._world.Isend([res.GetContiguousView(fr, fr + size), MPI.DOUBLE], destination, tag)
        return Handle(handle)
    
    def IRecv(self, res, fr, size, source, tag):
        handle = self._world.Irecv([res.GetContiguousView(fr, fr + size), MPI.DOUBLE], source, tag)
        return Handle(handle)
    
    def Barrier(self, x):
        self._world.Barrier()

    def AllReduceAnd(self, x, b):
        return self._world.allreduce(b, op=MPI.MAX)

    def Gather(self, root, part, whole, partFrom, partLen, wholeFrom, wholeLen, l):
        self._world.Barrier()
        self._world.Gather([part.GetContiguousView(partFrom, partFrom + partLen), MPI.DOUBLE],
                           [whole.GetContiguousView(wholeFrom, wholeFrom + wholeLen), MPI.DOUBLE],
                           root=root)

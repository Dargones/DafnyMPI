import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

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
import Spec as Spec
import math
import matplotlib
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    'pdf.fonttype' : 42,
    'ps.fonttype' : 42,
    'font.family' : 'serif',
    'text.usetex' : False,
    'font.size': 25,      
    'axes.labelsize': 25,  
    'xtick.labelsize': 12,  
    'ytick.labelsize': 12, 
    'legend.fontsize': 12,
    'figure.titlesize': 22,
    'lines.linewidth': 2   
})

# Module: ExternUtils

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Sqrt(val):
        return math.sqrt(val)
    
    @staticmethod
    def Pi():
        return math.pi
    
    @staticmethod
    def Sin(val):
        return math.sin(val)

    @staticmethod
    def Plot1D(u, filename, minx, maxx, miny, maxy, xname, yname):
        filename = _dafny.string_from_utf_16(filename)
        xname =  _dafny.string_from_utf_16(xname)
        yname =  _dafny.string_from_utf_16(yname)
        u = u.arr
        n = len(u)
        x = np.linspace(float(minx), float(maxx), n)
        plt.figure(figsize=(8, 6))
        plt.plot(x, u, linewidth=3)
        plt.xlabel(xname)#, fontsize=40)
        plt.ylabel(yname)#, fontsize=40)
        plt.xlim(float(minx), float(maxx))
        plt.ylim(float(miny), float(maxy))
        #plt.tick_params(axis='x', labelsize=36)
        #plt.tick_params(axis='y', labelsize=36)
        plt.grid(True)
        plt.tight_layout()
        plt.savefig(filename)
        plt.close()

    @staticmethod
    def Plot2D(u, filename, minx, maxx, miny, maxy, vmin, vmax, xname, yname):
        filename = _dafny.string_from_utf_16(filename)
        xname =  _dafny.string_from_utf_16(xname)
        yname =  _dafny.string_from_utf_16(yname)
        u = u.arr
        ny, nx = u.shape
        extent = [float(minx), float(maxx), float(miny), float(maxy)]
        plt.figure(figsize=(8, 6))
        if vmax == None or vmin == None:
            plt.imshow(u, origin='lower', extent=extent, aspect='auto')
        else:
            vmin = float(vmin)
            vmax = float(vmax)
            plt.imshow(u, origin='lower', extent=extent, aspect='auto', 
                    vmin=vmin, vmax=vmax)
        plt.colorbar()
        plt.xlabel(xname)#, fontsize=40)
        plt.ylabel(yname)#, fontsize=40)
        plt.tick_params(axis='x')#, labelsize=36)
        plt.tick_params(axis='y')#, labelsize=36)
        plt.tight_layout()
        plt.savefig(filename)
        plt.close()

    @staticmethod
    def Plot2DV2(u, filename, minx, maxx, miny, maxy, xname, yname):
        default__.Plot2D(u, filename, minx, maxx, miny, maxy, 
                         None, None, xname, yname)


(* ::Package:: *)


(******************************************************************************
       Copyright (C) 2010 Dario Malchiodi <malchiodi@di.unimi.it>

This file is part of xmlRPC.
xmlRPC is free software; you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free
Software Foundation; either version 2.1 of the License, or (at your option)
any later version.
xmlRPC is distributed in the hope that it will be useful, but without any
warranty; without even the implied warranty of merchantability or fitness
for a particular purpose. See the GNU Lesser General Public License for
more details.
You should have received a copy of the GNU Lesser General Public License
along with xmlRPC; if not, see <http://www.gnu.org/licenses/>.

******************************************************************************)

(* : Title : xmlRPC *)
(* : Context : xmlRPC` *)
(* : 
    Author : Dario Malchiodi *)
(* : Summary : XML - RPC client *)
(* : 
    Package Version : 1.0 *)
(* : Mathematica Version : 5.1 *)
(* : 
    Keywords : XML - RPC, remote procedure call *)

BeginPackage["xmlRPC`"]

xmlRPCInit::usage = \
"xmlRPCInit[address,port] sets the address and port of the XML-RPC server to be called";\

arrayDecode::usage = \
"arrayDecode[xml] transforms the array XML encoding contained in xml into a list";\

xmlRPCDecode::usage = \
"xmlRPCDecode[{type,value}] interpretes the data contained in value and returns the corresponding type in Mathematica";\

xmlRPCGetAnswer::usage = \
"xmlRPCGetAnser[xmlObj] returns the Mathematica expression corresponding to the XML encoding contained in the string xmlObj";\

xmlRPCPayload::usage = \
"xmlRPCPayload[methodName, params] returns the HTTP payload containing the XML encoding of a RPC call to the method methodName using the arguments contained in the list params";\

xmlRPCHeader::usage = \
"xmlRPCHeader[payload] returns the HTTP header corresponding to the payload contained in payload";\

xmlRPC::usage = \
"xmlRPC[methodName,params] executes the RPC to the method methodName using the arguments contained in the list params";\

base64EncodeTable::usage = \
"base64EncodeTable[n] returns the ASCII character corresponding to the value n in the base64 encoding";\

base64GroupEncode::usage = \
"base64GroupEncode[group] returns the four-character string  base64-encoding a group of three bytes";\

base64Encode::usage = \
"base64Encode[byt] returns the string base64-encoding the sequence of bytes byt";\

base64DecodeTable::usage = \
"base64DecodeTable[c] returns the byte corresponding to the ASCII character c in the base64 encoding";\

base64GroupDecode::usage = \
"base64GroupDecode[group] returns the three bytes corresponding to the base64-encoding whose bytes are in the list group";\

base64Decode::usage = \
"base64Decode[str] returns the string contained the base64-decoded version of the string str";\


xmlRPC::"error" = "`1`";

Begin["`Private`"]

Needs["JLink`"];

xmlRPCInit[server_, port_] := Block[{},
    $xmlRPCServer = server;
    $xmlRPCPort = port;
    JLink`InstallJava[]
    ]

base64DecodeTable[c_] := Which[
    FromCharacterCode[c] == "-", 63,
    FromCharacterCode[c] == "+", 62,
    ToCharacterCode["0"][[1]] <= c <= ToCharacterCode["9"][[1]],
    c - ToCharacterCode["0"][[1]] + 52,
    ToCharacterCode["a"][[1]] <= c <= ToCharacterCode["z"][[1]],
    c - ToCharacterCode["a"][[1]] + 26,
    ToCharacterCode["A"][[1]] <= c <= ToCharacterCode["Z"][[1]],
    c - ToCharacterCode["A"][[1]],
    FromCharacterCode[c] == "=", 0
    ]
base64GroupDecode[group_] := Block[{},
    FromDigits[#, 2] & /@ 
      Partition[IntegerDigits[#, 2, 6] & /@ group // Flatten, 8]
    ]
base64Decode[str_] := Block[{s},
    s = StringReplace[str, Whitespace -> ""];
    s = ToCharacterCode[
        StringReplace[s, n : Except["="] ... ~~ {"="} .. -> n]];
    (base64GroupDecode /@ Partition[base64DecodeTable/@s,4,4,{1,1},{}]) // Flatten
    ]
base64EncodeTable[n_] := Which[
    n == 0, "=",
    n < 26,
    FromCharacterCode[ToCharacterCode["A"] + n],
    n < 52,
    FromCharacterCode[ToCharacterCode["a"] + n - 26],
    n < 62,
    FromCharacterCode[ToCharacterCode["0"] + n - 52],
    n == 62, "+",
    n == 63, "-"
    ]
base64GroupEncode[group_] := Block[{},
    f = Partition[Map[IntegerDigits[#, 2, 8] &, group] // Flatten, 6];
    base64EncodeTable /@ Map[FromDigits[#, 2] &, f]
    ]
base64Encode[byt_] := Block[{b},
    b = byt;
    b = Join[b, Switch[Mod[Length[b], 3],
          0, {},
          1, {0, 0},
          2, {0}
          ]];
    StringExpression @@ (base64GroupEncode /@ Partition[b, 3] // Flatten)
    ]

Unprotect[ToDate];
ToDate[s_String] := StringSplit[strDate, {"-", "T", ":"}] // ToExpression
Protect[ToDate];
arrayDecode[value_] := 
  StringCases[StringReplace[value, "<data>" ~~ j___ ~~ "</data>" -> j], 
    ShortestMatch[
        Whitespace ... ~~ 
          "<value>" ~~ 
            Whitespace ... ~~ 
              "<" ~~ v : (Except[">"] ..) ~~ 
                  ">" ~~ j___ ~~ 
                      "</" ~~ 
                        Except[">"] .. ~~ 
                          ">" ~~ Whitespace ... ~~ "</value>"] -> 
      xmlRPCDecode[{v, j}]]

xmlRPCDecode[{type_, value_}] := Block[{},
    Switch[type,
      "i4" | "int" | "double", ToExpression[value],
      "boolean", If[value == "0", False, True],
      "dateTime.iso8601", ToDate[value],
      "base64", base64Decode[value]//FromCharacterCode,
      "array", arrayDecode[value],
      "struct", ImportString["<struct>" ~~ value ~~ "</struct>", "XML"],
      _, value
      ]
    ]

xmlRPCGetAnswer[xml_] :=
  xmlRPCDecode@
    StringReplace[
        xml, ___ ~~ 
            "<param>" ~~ 
              Whitespace ... ~~ 
                "<value>" ~~ 
                  Whitespace ... ~~ 
                    "<" ~~ v : Except[">"] .. ~~ 
                        ">" ~~ 
                          j___ ~~ 
                            "</" ~~ 
                              Except[">"] .. ~~ 
                                ">" ~~ 
                                  Whitespace ... ~~ 
                                    "</value>" ~~ 
                                      Whitespace ... ~~ 
                                        "</param>" ~~ ___ -> {v, j}][[1]]


xmlRPCPayload[methodName_, params_] := Block[{xmlObj},
    xmlObj = 
      ImportString["<?xml version=\"1.0\"?><methodCall><methodName/><params/></methodCall>",
         "XML"];
    xmlObj = 
      xmlObj /. 
        XMLElement["methodName", {}, {}] -> 
          XMLElement["methodName", {}, {methodName}];
    xmlObj = 
      xmlObj /. 
        XMLElement["params", {}, {}] -> 
          XMLElement["params", {}, 
            Map[XMLElement[
                  "param", {}, {XMLElement[
                      "value", {}, {XMLElement[#[[1]], {}, {#[[2]]}]}]}] &, 
              params]];
    Return[ExportString[xmlObj, "XML", "Entities"->"HTML"]];
    ]

xmlRPCHeader[payload_] := Block[{head},
    head = "POST /RPC2 HTTP/1.0\n";
    head = 
      head <> "User-Agent: Mathematica/" <> ToString[$VersionNumber] <> 
        " (" <> $System <> ")\n";
    head = head <> "Host: " <> $MachineName <> "." <> $MachineDomain <> "\n";
    head = head <> "Content-Type: text/xml\n";
    head = head <> "Content-length: ";
    head = head <> ToString[StringLength[payload]] <> "\n";
    Return[head <> "\n"];
    ]

Options[xmlRPC]={"verbose"->False};

xmlRPC[methodName_, params_, opts___] := 
  Block[{cli, out, in, payload, head, answer, fetch, retVal, error, verbose},
    verbose = "verbose" /. {opts} /. Options[xmlRPC];
    cli = JLink`JavaNew["java.net.Socket", $xmlRPCServer, $xmlRPCPort];
    out = JLink`JavaNew["java.io.DataOutputStream", cli@getOutputStream[]];
    in = JLink`JavaNew["java.io.DataInputStream", cli@getInputStream[]];
    If[verbose==True,Print["Used socket: ", cli]];
    
    payload = xmlRPCPayload[methodName, params];
    head = xmlRPCHeader[payload];
    
    If[verbose==True,Print["Sending:\n",head<>payload]];
    out@writeBytes[head <> payload];
    If[verbose==True,Print["Packet sent"]];
    
    If[verbose==True,Print["Waiting answer"]];
    answer = "";
    fetch = in@readLine[];
    While[StringQ[fetch],
      answer = answer <> fetch <> "\n";
      fetch = in@readLine[];
      ];
    
    out@close[];
    in@close[];
    cli@close[];
    
    If[verbose==True,Print["Received:\n",answer]];
    
    If[verbose==True,Print["Decoding answer"]];
    If[StringMatchQ[answer, ___ ~~ "<params>" ~~ ___ ~~ "</params>" ~~ ___],
      retVal = 
        StringReplace[answer, 
          RegularExpression["(.|\n)*?\n\n((.|\n)*)"] -> "$2"];
      Return[xmlRPCGetAnswer[retVal]],
      error = 
        StringReplace[
          answer, ___ ~~ 
              "<int>" ~~ 
                fc__ ~~ 
                  "</int>" ~~ ___ ~~ 
                      "<string>" ~~ fs__ ~~ "</string>" ~~ ___ -> 
            "<error>" ~~ fc ~~ ":" ~~ fs ~~ "</error>"];
      
      Message[xmlRPC::"error", 
        ImportString[error, "XML"] /. 
          XMLObject[_][_, XMLElement[_, _, {s_}], _] -> s];
      Return[$Failed]
      ]
    ]

End[]

EndPackage[]

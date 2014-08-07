% -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
% Warning: this file was automatically generated. Edit with care
% -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-

% -*-LaTeX-*-



\definecolor{darkgray}{gray}{.5}
\definecolor{lightgray}{gray}{.75}

\newcommand{\maxwidthparbox}[2]{
  \newbox\tempbox
  \setbox\tempbox\hbox{#2}
  \ifdim\wd\tempbox>#1 \parbox{#1}{#2} \else \parbox{\wd\tempbox}{#2} \fi
  }

% Define a command for drawing labelled arrows (pointing right)
% \arrowr{(x,y)}{arrow length}{angle}{parbox maximum length}{label}{left ratio}{right ratio}
\newcommand\arrowr[7]{%
  \put#1{\rotatebox{#3}{%
         \raisebox{-\fontdimen22\textfont2}[0pt][0pt]{%
          \makebox[#2\unitlength][l]{%
          \leaders\hbox{$\!-\!$}\hskip 0pt plus #6fill%
              \scalebox{0.75}{%
                \maxwidthparbox{#4\unitlength}{\raggedright\textbf{#5}}}%
          \leaders\hbox{$\!-\!$}\hskip 0pt plus #7fill%
          $\mskip-12mu\rightarrow$}}}}}


% Define a command for drawing labelled arrows (pointing left)
% \arrowl{(x,y)}{arrow length}{angle}{parbox maximum length}{label}{left ratio}{right ratio}
\newcommand\arrowl[7]{%
  \put#1{\rotatebox{#3}{%
         \raisebox{-\fontdimen22\textfont2}[0pt][0pt]{%
          \makebox[#2\unitlength][l]{%
          \leaders\hbox{$\!-\!$}\hskip 0pt plus #6fill%
              \scalebox{0.75}{%
                \rotatebox{180}{
                 \raisebox{-4\unitlength}[0pt][0pt]{
                   \maxwidthparbox{#4\unitlength}{\raggedright\textbf{#5}}}}}%
          \leaders\hbox{$\!-\!$}\hskip 0pt plus #7fill%
          $\mskip-12mu\rightarrow$}}}}}


% Define a command for drawing unlabelled arrows
% \arrowu{(x,y)}{length}{angle}
\newcommand\arrowu[3]{%
  \put#1{\rotatebox{#3}{%
         \raisebox{-\fontdimen22\textfont2}[0pt][0pt]{%
          \makebox[#2\unitlength][l]{%
          \leaders\hbox{$\!-\!$}\hfill%
          $\mskip-12mu\rightarrow$}}}}}


% Define a command for drawing line
% \rline{(x,y)}{length}{angle}
\newcommand\rline[3]{%
  \put#1{\rotatebox{#3}{%
          \raisebox{-\fontdimen22\textfont2}[0pt][0pt]{%
          \makebox[#2\unitlength][l]{\leaders\hbox{$\!-\!$}\hfill}%
        }}}}


% Define a command for placing text
% \rtext{(x,y)}{maximum width}{angle}{string}
\newcommand\rtext[4]{%
  \put#1{\rotatebox{#3}{%
        \maxwidthparbox{#2\unitlength}{\small\raggedright #4}%
        }}}

% Define a command for drawing filled circles
% \disc{(x,y)}{diam}
\newcommand\disc[2]{%
  \put#1{\color{darkgray}\circle*{#2}}%
  }

% Define a command for preparing new picture environment pages
% \preppage{xpos 1st vertical line}{xpos 2nd vertical line}{page height}
\newcommand\preppage[3]{%
   {\color{lightgray}\rline{(#1,0)}{#3}{90}\rline{(#2,0)}{#3}{90}}%
}

\newcommand{\labeldgram}[1]{#1}
\newcommand{\labelbetween}[1]{\quad{}#1}

%tasteless visual formatting:
\newcommand{\labelenbox}[2]{\makebox[12cm][l]{#1\hfill\bfseries{}#2}}

\newcommand{\labelcall}[2]{\labelenbox{#1}{#2}}
\newcommand{\labelret}[2]{\labelenbox{#1}{#2}}




% Start document
%\setlength{\unitlength}{0.9pt}
%\scalebox{0.67}{{%\fbox{

\setlength{\unitlength}{0.9pt}
% -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
% Start of page 1
% -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
\scalebox{0.67}{
\begin{picture}(730,1000)
\rtext{(5,980)}{725}{0}{\textnormal\bfseries Test Host: BSD(john)  Aux Host: LINUX(alan)\newline Test Description: [TCP normal] Demonstration: create a listening socket on the auxiliary host; create a socket on the local host and connect to the listening socket; accept the connection; send a string and then receive the string on the auxiliary host; close both sockets (no tcpcb) \newline\small /usr/groups/tthee/batch/demo-traces/trace5002}
\rtext{(0,930)}{395}{0}{\labelcall{\labelstepZ}{socket(SOCK\textunderscore{}STREAM)}}
\disc{(400,930)}{4}
\rtext{(0,905)}{395}{0}{\labelbetween{\labelstepZb}}
\rtext{(0,880)}{395}{0}{\labelret{\labelstepII}{OK(FD 8)}}
\rtext{(0,855)}{395}{0}{\labelbetween{\labelstepIIb}}
\disc{(400,880)}{4}
\rtext{(0,830)}{395}{0}{\labelcall{\labelstepIV}{bind(FD 8, SOME(IP 192 168 0 12), SOME(Port 3333))}}
\disc{(400,830)}{4}
\rtext{(0,805)}{395}{0}{\labelbetween{\labelstepIVb}}
\rtext{(0,780)}{395}{0}{\labelret{\labelstepVI}{OK()}}
\rtext{(0,755)}{395}{0}{\labelbetween{\labelstepVIb}}
\disc{(400,780)}{4}
\rtext{(0,730)}{395}{0}{\labelcall{\labelstepVIII}{listen(FD 8, 3)}}
\disc{(400,730)}{4}
\rtext{(0,705)}{395}{0}{\labelbetween{\labelstepVIIIb}}
\rtext{(0,680)}{395}{0}{\labelret{\labelstepX}{OK()}}
\rtext{(0,655)}{395}{0}{\labelbetween{\labelstepXb}}
\disc{(400,680)}{4}
\disc{(700,630)}{4}
\rtext{(0,630)}{395}{0}{\labeldgram{\labelstepXII}}
\rtext{(0,605)}{395}{0}{\labelbetween{\labelstepXIIb}}
\arrowl{(400,630)}{301}{185}{258}{TCP 959699258:0 (0:0)  \color{lightgray}U\color{lightgray}A\color{lightgray}P\color{lightgray}R\color{black}S\color{lightgray}F\color{black} \newline 192.168.0.14:3333$\rightarrow$192.168.0.12:3333 win=5840 ws=0 urp=0 mss=1460 ts=78281764,0 len=0 }{0.10}{0.90}
\disc{(400,580)}{4}
\rtext{(0,580)}{395}{0}{\labeldgram{\labelstepXIV}}
\rtext{(0,555)}{395}{0}{\labelbetween{\labelstepXIVb}}
\arrowr{(400,580)}{301}{355}{258}{TCP 2706264489:959699259 (0:1)  \color{lightgray}U\color{black}A\color{lightgray}P\color{lightgray}R\color{black}S\color{lightgray}F\color{black} \newline 192.168.0.12:3333$\rightarrow$192.168.0.14:3333 win=57344 ws=0 urp=0 mss=1460 ts=572707373,78281764 len=0 }{0.30}{0.70}
\disc{(700,530)}{4}
\rtext{(0,530)}{395}{0}{\labeldgram{\labelstepXVI}}
\rtext{(0,505)}{395}{0}{\labelbetween{\labelstepXVIb}}
\arrowl{(400,530)}{301}{185}{258}{TCP 959699259:2706264490 (1:1)  \color{lightgray}U\color{black}A\color{lightgray}P\color{lightgray}R\color{lightgray}S\color{lightgray}F\color{black} \newline 192.168.0.14:3333$\rightarrow$192.168.0.12:3333 win=5840 ws=* urp=0 mss=* ts=78281765,572707373 len=0 }{0.10}{0.90}
\rtext{(0,480)}{395}{0}{\labelcall{\labelstepXVIII}{accept(FD 8)}}
\disc{(400,480)}{4}
\rtext{(0,455)}{395}{0}{\labelbetween{\labelstepXVIIIb}}
\rtext{(0,430)}{395}{0}{\labelret{\labelstepXX}{OK(FD 9, (IP 192 168 0 14, Port 3333))}}
\rtext{(0,405)}{395}{0}{\labelbetween{\labelstepXXb}}
\disc{(400,430)}{4}
\disc{(700,380)}{4}
\rtext{(0,380)}{395}{0}{\labeldgram{\labelstepXXII}}
\rtext{(0,355)}{395}{0}{\labelbetween{\labelstepXXIIb}}
\arrowl{(400,380)}{301}{185}{258}{TCP 959699259:2706264490 (1:1)  \color{lightgray}U\color{black}A\color{black}P\color{lightgray}R\color{lightgray}S\color{lightgray}F\color{black} \newline 192.168.0.14:3333$\rightarrow$192.168.0.12:3333 win=5840 ws=* urp=0 mss=* ts=78281814,572707373 len=6 }{0.10}{0.90}
\rtext{(0,330)}{395}{0}{\labelcall{\labelstepXXIV}{recv(FD 9, 6, [])}}
\disc{(400,330)}{4}
\rtext{(0,305)}{395}{0}{\labelbetween{\labelstepXXIVb}}
\rtext{(0,280)}{395}{0}{\labelret{\labelstepXXVI}{OK("Hello!", NONE)}}
\rtext{(0,255)}{395}{0}{\labelbetween{\labelstepXXVIb}}
\disc{(400,280)}{4}
\disc{(700,230)}{4}
\rtext{(0,230)}{395}{0}{\labeldgram{\labelstepXXVIII}}
\rtext{(0,205)}{395}{0}{\labelbetween{\labelstepXXVIIIb}}
\arrowl{(400,230)}{301}{185}{258}{TCP 959699265:2706264490 (7:1)  \color{lightgray}U\color{black}A\color{lightgray}P\color{lightgray}R\color{lightgray}S\color{black}F \newline 192.168.0.14:3333$\rightarrow$192.168.0.12:3333 win=5840 ws=* urp=0 mss=* ts=78281815,572707373 len=0 }{0.10}{0.90}
\disc{(400,180)}{4}
\rtext{(0,180)}{395}{0}{\labeldgram{\labelstepXXX}}
\rtext{(0,155)}{395}{0}{\labelbetween{\labelstepXXXb}}
\arrowr{(400,180)}{301}{355}{258}{TCP 2706264490:959699266 (1:8)  \color{lightgray}U\color{black}A\color{lightgray}P\color{lightgray}R\color{lightgray}S\color{lightgray}F\color{black} \newline 192.168.0.12:3333$\rightarrow$192.168.0.14:3333 win=57920 ws=* urp=0 mss=* ts=572707424,78281814 len=0 }{0.30}{0.70}
\color{darkgray}\rline{(400,947)}{817}{270}\color{black}
\color{darkgray}\rline{(700,947)}{817}{270}\color{black}
\end{picture}

}
%}
%}

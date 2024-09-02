Verwendung:

1. Speichern Sie die Datei "BA_Titelseite.sty" in dem Verzeichnis in dem sich auch Ihre Bachelorarbeit befindet.
2. Fügen Sie folgende Einträge im Header Ihrer Bachelorarbeit hinzu und ändern Sie die Variablen.

\usepackage{BA_Titelseite}

%Namen des Verfassers der Arbeit
\author{X Y}
%Geburtsdatum des Verfassers
\geburtsdatum{1. April 1900}
%Gebortsort des Verfassers
\geburtsort{Bonn}
%Datum der Abgabe der Arbeit
\date{\today}

%Name des Betreuers
% z.B.: Prof. Dr. Peter Koepke
\betreuer{Betreuer: Prof. Dr. X Y}
%Name des Zweitgutachters
\zweitgutachter{Zweitgutachter: Prof. Dr. X Y}
%Name des Instituts an dem der Betreuer der Arbeit tätig ist.
%z.B.: Mathematisches Institut
\institut{Mathematisches Institut}
%\institut{Institut f\"ur Angewandte Mathematik}
%\institut{Institut f\"ur Numerische Simulation}
%\institut{Forschungsinstitut f\"ur Diskrete Mathematik}
%Titel der Bachelorarbeit
\title{This is only an example}
%Do not change!
\ausarbeitungstyp{Bachelorarbeit Mathematik}

3. Mit "\maketitle" können Sie jetzt die Titelseite generieren lassen.

import React from "react";

type Props = { title: string; onClick?: (value: string) => void };

export const Component: React.FC<Props> = ({ title, onClick }) => {
  return (
    <button onClick={() => onClick && onClick(title)}>{title}</button>
  );
};

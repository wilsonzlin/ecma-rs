import type { ComponentProps, FC, PropsWithChildren, ReactNode } from "./react";
import { createElement } from "./react";

export type ButtonProps = PropsWithChildren<{
  label: string;
  disabled?: boolean;
}>;

export const Button: FC<ButtonProps> = (props) => {
  const child: ReactNode = props.children;
  const disabled = props.disabled ? true : false;
  return createElement(
    "button",
    { disabled, onClick: (_e) => {} },
    props.label,
    child,
  );
};

export type NativeButtonProps = ComponentProps<"button">;

export const DEFAULT_BUTTON_PROPS: NativeButtonProps = {
  disabled: true,
  onClick: (_e) => {},
};


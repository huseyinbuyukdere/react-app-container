/// <reference types="react" />
interface IconComponentProps {
    name: string;
    height?: number;
    width?: number;
    fill?: string;
    className?: string;
    style?: any;
}
declare const IconComponent: (props: IconComponentProps) => JSX.Element;
export default IconComponent;
